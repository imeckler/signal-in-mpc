#!/usr/bin/env python3
"""Scoped closed-Self/dictionary specialization before mutable-borrow shaping."""
from pathlib import Path
import sys
src=Path(sys.argv[1]);p=src/'src/transform/normalize/partial_monomorphization.rs';s=p.read_text()
# Only the actual one-copy adapter and its minimal regression are eligible.
helper='''
fn closed_content_type(ty: &Ty) -> bool {
    match ty.kind() {
        TyKind::Literal(_) => true,
        TyKind::Adt(tref) => tref.generics.regions.is_empty()
            && tref.generics.const_generics.is_empty()
            && tref.generics.trait_refs.is_empty()
            && tref.generics.types.iter().all(closed_content_type),
        _ => false,
    }
}
fn closed_adapter_target(ctx: &TransformCtx, id: ItemId) -> bool {
    if !matches!(id, ItemId::Fun(_)) { return false; }
    let Some(item) = ctx.translated.get_item(id) else { return false; };
    let name = item.item_meta().name.with_ctx(&ctx.into_fmt()).to_string();
    name.ends_with("::encoding::bytes::merge_one_copy")
        || name == "borrow_clause_regression::merge"
}
'''
s=s.replace('type MutabilityShape = Binder<GenericArgs>;', 'type MutabilityShape = Binder<GenericArgs>;\n'+helper)
s=s.replace('''    specialize_adts: bool,''','''    specialize_adts: bool,
    closed_adapter_ids: HashSet<ItemId>,''',1)
s=s.replace('''        PartialMonomorphizer {
            ctx,''','''        let closed_adapter_ids = ctx.translated.all_ids()
            .filter(|id| closed_adapter_target(ctx, *id)).collect();
        PartialMonomorphizer {
            closed_adapter_ids,
            ctx,''',1)
s=s.replace('''        args: &GenericArgs,
    ) -> (MutabilityShape, GenericArgs)''','''        args: &GenericArgs,
        closed_self: bool,
    ) -> (MutabilityShape, GenericArgs)''')
s=s.replace('''        let _ = VisitWithBinderDepth::new(&mut builder).visit(&mut shape_contents);''','''        if closed_self {
            let _ = VisitWithBinderDepth::new(&mut builder).visit(&mut shape_contents.regions);
            for ty in shape_contents.types.iter_mut().skip(1) {
                let _ = VisitWithBinderDepth::new(&mut builder).visit(ty);
            }
            let _ = VisitWithBinderDepth::new(&mut builder).visit(&mut shape_contents.const_generics);
        } else {
            let _ = VisitWithBinderDepth::new(&mut builder).visit(&mut shape_contents);
        }''')
s=s.replace('''        let shape_params = {''','''        let mut shape_params = {''',1)
s=s.replace('''        let shape_args = builder.extracted;
        let shape = Binder::new''','''        let mut shape_args = builder.extracted;
        if closed_self {
            // The first original clause is a closed, explicitly supplied impl.
            // Substitute it into the body; preserve every region/outlives bound
            // and renumber only the remaining dictionary parameters.
            let mut remap = shape_params.identity_args();
            let mut kept: IndexVec<TraitClauseId, TraitParam> =
                shape_params.trait_clauses.iter().skip(1).cloned().collect();
            for (i, clause) in kept.iter_mut_enumerated() { clause.clause_id = i; }
            remap.trait_refs[TraitClauseId::ZERO] = args.trait_refs[TraitClauseId::ZERO].clone();
            for (i, tref) in remap.trait_refs.iter_mut_enumerated().skip(1) {
                *tref = kept[TraitClauseId::from_usize(i.index() - 1)]
                    .identity_tref_at_depth(DeBruijnId::ZERO);
            }
            shape_contents = shape_contents.substitute(&remap);
            shape_params.trait_clauses = kept;
            shape_params = shape_params.substitute(&remap);
            shape_args.trait_refs = shape_args.trait_refs.into_iter().skip(1).collect();
        }
        let shape = Binder::new''')
s=s.replace('''        if !generics.types.iter().any(|ty| self.is_infected(ty)) {
            return None;
        }''','''        let closed_self = self.closed_adapter_ids.contains(&id)
            && generics.types.len() == 2 && generics.trait_refs.len() == 2
            && closed_content_type(&generics.types[TypeVarId::ZERO])
            && matches!(&generics.trait_refs[TraitClauseId::ZERO].kind,
                TraitRefKind::TraitImpl(iref) if iref.generics.is_empty());
        if !closed_self && !generics.types.iter().any(|ty| self.is_infected(ty)) {
            return None;
        }''',1)
s=s.replace('''MutabilityShapeBuilder::compute_shape(self, item_params, generics);''','''MutabilityShapeBuilder::compute_shape(self, item_params, generics, closed_self);''')
s=s.replace('''        let _ = item.drive_mut(self);''','''        // Keep an original template unchanged once all actual callers are
        // being redirected to closed-dictionary specializations. It is removed
        // below only after a whole-crate reference check succeeds.
        if self.closed_adapter_ids.contains(&item.as_ref().id())
            && !self.reverse_shape_map.contains_key(&item.as_ref().id())
            && self.partial_mono_shapes.keys().any(|(base, _)| *base == item.as_ref().id()) {
            return;
        }
        let _ = item.drive_mut(self);''',1)
# Resolve only statically known impls, using the pre-existing binder-aware resolver.
s=s.replace("    fn enter_fn_ptr(&mut self, x: &mut FnPtr) {", "    fn enter_fn_ptr(&mut self, x: &mut FnPtr) {\n        if let FnPtrKind::Trait(tref, _) = x.kind.as_mut() { super::normalize_trait_refs::normalize_known_parent(self.ctx, tref); }\n        if let Some(resolved) = super::skip_trait_refs_when_known::normalize_method_call_on_known_impl(self.ctx, x) { *x = resolved; }")
check = """        if matches!(*x.kind, FnPtrKind::Trait(..))
            && x.generics.types.iter().any(|ty| self.is_infected(ty)) {
            register_error!(self.ctx, self.span,
                "partial monomorphization of generic trait methods with mutable-borrow arguments is unsupported; method and implementation specialization is required");
        }
"""
s=s.replace("    fn exit_fn_ptr(&mut self, x: &mut FnPtr) {", "    fn exit_fn_ptr(&mut self, x: &mut FnPtr) {\n"+check,1)
# Reference-based deletion of unused original free-function templates.
append='''
        #[derive(Visitor, Default)]
        struct Uses { ids: HashSet<FunDeclId> }
        impl VisitAst for Uses {
            fn enter_fn_ptr(&mut self, ptr: &FnPtr) {
                if let FnPtrKind::Fun(FunId::Regular(id)) = *ptr.kind { self.ids.insert(id); }
            }
            fn enter_fun_decl_ref(&mut self, ptr: &FunDeclRef) { self.ids.insert(ptr.id); }
        }
        let mut uses = Uses::default();
        for item in visitor.ctx.translated.all_items() { let _ = item.drive(&mut uses); }
        let obsolete: Vec<ItemId> = visitor.partial_mono_shapes.keys()
            .map(|(base,_)| *base)
            .filter(|id| visitor.closed_adapter_ids.contains(id))
            .filter(|id| matches!(id, ItemId::Fun(fid) if !uses.ids.contains(fid)))
            .collect();
        for id in obsolete { let _ = visitor.ctx.translated.remove_item_temporarily(id); }
        let residual: Vec<_> = visitor.closed_adapter_ids.iter().copied()
            .filter(|id| matches!(id, ItemId::Fun(fid) if uses.ids.contains(fid)))
            .filter(|id| visitor.partial_mono_shapes.keys().any(|(base,_)| base == id))
            .collect();
        for _id in residual {
            register_error!(visitor.ctx, Span::dummy(),
                "closed adapter specialization leaves an abstract caller; generic borrowed trait method support is required");
        }
'''
marker='''            visitor.ctx.translated.put_item_back(id, decl);
        }
''';assert s.count(marker)==1;s=s.replace(marker,marker+append)
p.write_text(s)
p=src/'src/transform/normalize/skip_trait_refs_when_known.rs';s=p.read_text();s=s.replace('fn normalize_method_call_on_known_impl(', 'pub(crate) fn normalize_method_call_on_known_impl(');p.write_text(s)

p=src/'src/transform/normalize/normalize_trait_refs.rs';s=p.read_text();s += """
/// Reuse the existing binder-aware parent proof normalization after a closed
/// adapter substitution. No trait evidence is invented.
pub(crate) fn normalize_known_parent(ctx: &TransformCtx, tref: &mut TraitRef) {
    let impl_parent_refs = ctx.translated.trait_impls.map_ref(|timpl| timpl.implied_trait_refs.clone());
    let _ = NormalizeTraitRefs { impl_parent_refs: &impl_parent_refs, steps: 0 }.visit(tref);
}
""";p.write_text(s)
