"""Same-VM KEM-producing PQXDH composition, with explicit validation input.

The caller must supply shared status255 only after identity/signed-prekey policy
validation. That policy and XEdDSA implementation are still separate work.
Neither KEM acceptance, DH values, identifiers, derived keys nor ciphertext are
opened here. Public profile selects optional one-time prekey presence.
"""
from handshake_backend import mixed
from handshake_backend.field_dag import validate


def _wire(kem, image, mode, raw, primitives):
    if kem.rank not in (3,4) or (kem.rank==3 and not kem.kyber):raise ValueError('unsupported Signal KEM profile')
    variant=('kyber' if kem.kyber else 'mlkem')+str(768 if kem.rank==3 else 1024)
    if image.get('name')!='signal-kem-wire-'+mode+'-'+variant or image.get('input_bits')!=len(raw):
        raise ValueError('incorrect typed KEM artifact')
    return primitives.execute_boolean(image,raw)


def _agreement(field_image,private,public,primitives):
    if len(private)!=256 or len(public)!=256:raise ValueError('X25519 input32')
    scalar=primitives.wire_bits_to_scalar_fields(private)
    point=primitives.wire_bits_to_field(public,mask_high_bit=True)
    return primitives.field_to_wire_bits(primitives.execute_secret(field_image,scalar+[point])[0])


def _derive(field_image,kdf_image,pairs,kem_secret,validation_status,kem_status,primitives):
    validate(field_image)
    if (field_image['input_count']!=257 or field_image['bit_inputs']!=list(range(256))
            or len(field_image['outputs'])!=1):raise ValueError('X25519 artifact')
    profile='present' if len(pairs)==4 else 'none'
    if (len(pairs) not in (3,4) or kdf_image.get('name')!='signal-pqxdh-'+profile
            or kdf_image.get('input_bits')!=256*(len(pairs)+1)
            or len(kdf_image.get('outputs',[]))!=768):raise ValueError('PQXDH artifact')
    if len(validation_status)!=8 or len(kem_secret)!=256:raise ValueError('shared status/KEM32')
    accepted=kem_status
    for bit in validation_status:accepted=accepted&bit
    values=[]
    for private,public in pairs:
        agreement=_agreement(field_image,private,public,primitives)
        nonzero=agreement[0]
        for bit in agreement[1:]:nonzero=nonzero^bit^(nonzero&bit)
        accepted=accepted&nonzero;values+=agreement
    keys=primitives.execute_boolean(kdf_image,values+list(kem_secret))
    return accepted,[bit&accepted for bit in keys]


def initiate(kem,wire_image,field_image,kdf_image,identity_private,ephemeral_private,
             their_identity,signed_prekey,one_time_prekey,serialized_kem_public,kem_entropy,
             validation_status,*,primitives=mixed):
    rank=kem.rank;pkbits=8*(384*rank+33);ctbits=8*(32*(kem.du*rank+kem.dv)+1)
    if len(serialized_kem_public)!=pkbits or len(kem_entropy)!=256:raise ValueError('typed KEM input')
    candidate=kem.encapsulate(list(serialized_kem_public[8:])+list(kem_entropy))
    zero=candidate[0]^candidate[0]
    framed=_wire(kem,wire_image,"encapsulate",list(serialized_kem_public[:8])+[zero]*8+candidate,primitives)
    if len(framed)!=8+ctbits+256:raise ValueError('typed KEM output')
    pairs=[(identity_private,signed_prekey),(ephemeral_private,their_identity),(ephemeral_private,signed_prekey)]
    if one_time_prekey is not None:pairs.append((ephemeral_private,one_time_prekey))
    accepted,keys=_derive(field_image,kdf_image,pairs,framed[8+ctbits:],validation_status,framed[0],primitives)
    return [accepted]*8+keys+[bit&accepted for bit in framed[8:8+ctbits]]


def accept(kem,wire_image,field_image,kdf_image,identity_private,signed_prekey_private,
           one_time_private,their_identity,their_ephemeral,serialized_kem_secret,serialized_ciphertext,
           validation_status,*,primitives=mixed):
    rank=kem.rank;skbits=8*(768*rank+97);ctbits=8*(32*(kem.du*rank+kem.dv)+1)
    if len(serialized_kem_secret)!=skbits or len(serialized_ciphertext)!=ctbits:raise ValueError('typed KEM input')
    candidate=kem.decapsulate(list(serialized_kem_secret[8:])+list(serialized_ciphertext[8:]))
    framed=_wire(kem,wire_image,"decapsulate",list(serialized_kem_secret[:8])+list(serialized_ciphertext[:8])+candidate,primitives)
    if len(framed)!=264:raise ValueError('typed KEM output')
    pairs=[(signed_prekey_private,their_identity),(identity_private,their_ephemeral),(signed_prekey_private,their_ephemeral)]
    if one_time_private is not None:pairs.append((one_time_private,their_ephemeral))
    accepted,keys=_derive(field_image,kdf_image,pairs,framed[8:],validation_status,framed[0],primitives)
    return [accepted]*8+keys
