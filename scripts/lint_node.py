#!/usr/bin/env python3
"""The guard-rail lints of REORGANIZATION_PLAN.md (stage S0). Reads the tree only; builds nothing.

    lint_node.py                     run the checks that are switched on; exit 1 on a finding
    lint_node.py --report            also print what the checks see (counts, worst files)
    lint_node.py --update-baseline   rewrite the I/O baseline from the tree as it is (ratchet down
                                     after a stage moved sites into Channels; never to add sites)
    lint_node.py --enable secret-val,message-fields   switch on checks of later stages

Checks:
  io-baseline (a)       The I/O primitive sites of the controller: every Lean module the
                        controller's executable imports from this repository (its import
                        closure, recomputed each run). Files the plan allows to do I/O
                        (TlsMpc/Node/Channels.lean and Worker.lean) may have any number. Every
                        other file may have at most the count recorded per primitive in
                        scripts/lint_node_baseline.json (today's sites); a new site, or a site
                        in a file new to the closure, fails. Since S4, `IO.getEnv` appears exactly
                        once in the closure: in `Config.read`, TlsMpc/Node/Channels.lean.
                        Since S5 (strict): the controller's own file and every other module under
                        TlsMpc/Node may have NO site, and the baseline may not list them; what is
                        left in the baseline is the worker spawn (TlsWorkerProcess: later
                        `Worker.lean`, stages S8-S9; since S6 TlsWorker has none, its polling
                        transports being in the flow API). A `Namespace.metadata`-style
                        call (an uppercase qualifier) is not counted as a FilePath dot call.
  escape-hatches (b)    No sorry, admit, native_decide, bv_decide, ofReduceBool, implemented_by,
                        extern, unsafe, opaque, axiom, csimp, skipKernelTC or partial def in
                        TlsMpc/Node (plan, rule 6 and section 4.1).
  emitter-isolation (c) No circuit emitter's import closure contains a module under TlsMpc.Node
                        (plan, rule 4: the circuit cache is keyed by the emitter binary). The
                        emitters: every lean_exe of lakefile.toml named *_emitter, and
                        circuit_inventory.
  secret-val (d)        On since S4. `Secret.val` / `Secret.mk` / `expose` (the one public accessor of
                        TlsMpc/Node/Secret.lean, its field and constructor being private) only in
                        the eliminators' files (plan 4.1): Secret.lean, Engine.lean, Channels.lean,
                        Reveal.lean, Local/*.
  message-fields (d)    On since S5. Messages.lean mentions neither `Secret` nor `Handle` outside
                        comments and strings (plan 3.1). Inside Lean, `Messages.checkPublic` (run at
                        the end of Messages.lean, so the build fails) checks the same by type,
                        transitively through every repository type a message field uses.
  flow-calls            On since S6. In the controller and every TlsMpc/Node module of its import
                        closure, the worker is reached only through the flow API
                        (TlsMpc/Node/Flow.lean): a call on the worker pipe (`.call`, `.pipe`,
                        `.recording`), the old `TlsWorker` bindings (`emptyReply`, `backend`,
                        `connectVia`, `onConnection`, ...), an operation code (`TlsWorkerPipe.code`),
                        `Legacy.*`, `inputOwn` (own private input, Secret.lean's eliminator) and the
                        `Reveal.*` wrappers (the only makers of `Opened`) appear only in the legacy
                        flow implementations (TlsMpc/Node/Flows/*Legacy.lean, Flows/Legacy.lean),
                        since S9 in the script implementations of the same flows (Flows/*Backend.lean,
                        Flows/Runner.lean, Flows/Select.lean) and where they are defined
                        (Secret.lean, Reveal.lean; Channels.lean for operation 39, the peer channel).
  session-state         On since S7. The controller's executable root
                        (handshake_backend/EmpHybridWork/PublicServiceController.lean) is only
                        `import TlsMpc.Node.Main` and `def main := TlsMpc.Node.Main.main`; the session
                        code is TlsMpc/Node/Main.lean and TlsMpc/Node/Session/*.lean, which the
                        io-baseline (strict) and flow-calls checks cover as every TlsMpc/Node file.
                        Session state is threaded explicitly (`Session.State`, P4): `IO.Ref`,
                        `IO.mkRef` and `ST.Ref` appear in Session/*.lean only in State.lean (the
                        `Connection` type: a connection's receive slot), Pool.lean and Start.lean
                        (where a connection and its slot are made); Main.lean may hold the worker
                        spawn's certificate result.
  ordering-sites        On since 2026-11-12 (PROOF_GAPS.md C3; Session/Events.lean, header, item 2).
                        The ordering theorems (ORD-1, ORD-2) are about the session's monad-generic
                        definitions, whose message requests and scratch commits are fields of the
                        operations records; they say nothing about a request or commit made
                        elsewhere. So, in the controller and every TlsMpc/Node module of its import
                        closure: `Flow.Send.request` and `Flow.Send.requestDevices` appear exactly
                        once each, in TlsMpc/Node/Session/Send.lean (the record `sendReal`), and
                        `Flow.Refresh.scratchCommit` exactly once, in TlsMpc/Node/Session/Store.lean
                        (`storeReal`); no file but the flows that define them names them unqualified
                        (`Send.request` …) or opens `TlsMpc.Node.Flow`, `Flow.Send` or `Flow.Refresh`.
                        (The operation codes behind them are reachable only through `Legacy.call`,
                        which flow-calls confines to the legacy flow files.)

Comments and string literals are ignored. Patterns are textual: an `open IO.FS` (or similar)
followed by an unprefixed call would hide a site, so such an `open` is itself reported as a
finding in the checked files.
"""
import argparse, json, os, re, sys, tomllib

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BASELINE = os.path.join(ROOT, 'scripts', 'lint_node_baseline.json')
CONTROLLER_EXE = 'public_service_controller'
NODE_DIR = 'TlsMpc/Node'
IO_ALLOWED = {'TlsMpc/Node/Channels.lean', 'TlsMpc/Node/Worker.lean'}
CONFIG_READER = 'TlsMpc/Node/Channels.lean'   # Config.read, the one IO.getEnv (stage S4)
SECRET_ALLOWED = re.compile(r'^TlsMpc/Node/(Secret|Engine|Channels|Reveal)\.lean$|^TlsMpc/Node/Local/')
ALL_CHECKS = ['io-baseline', 'escape-hatches', 'emitter-isolation', 'secret-val', 'message-fields', 'flow-calls', 'session-state',
              'ordering-sites']
DEFAULT_ON = ['io-baseline', 'escape-hatches', 'emitter-isolation', 'secret-val', 'message-fields', 'flow-calls', 'session-state',
              'ordering-sites']
# 2026-11-12 (check ordering-sites): the one call site of each effect the ordering theorems constrain.
ORDERING_SITES = {
    'Flow.Send.request': 'TlsMpc/Node/Session/Send.lean',
    'Flow.Send.requestDevices': 'TlsMpc/Node/Session/Send.lean',
    'Flow.Refresh.scratchCommit': 'TlsMpc/Node/Session/Store.lean',
}
ORDERING_DEFINED = {'TlsMpc/Node/Flows/SendLegacy.lean', 'TlsMpc/Node/Flows/RefreshLegacy.lean'}
ORDERING_BARE = re.compile(r'(?<![\w.])(?:Send\.(?:request|requestDevices)|Refresh\.scratchCommit)\b')
ORDERING_OPEN = re.compile(r'^\s*open\b[^\n]*\bFlow(?:\.Send|\.Refresh)?\b(?![\w.])', re.M)
# Stage S7: the executable root, and where a session may hold a reference (check session-state).
CONTROLLER_ROOT = 'handshake_backend/EmpHybridWork/PublicServiceController.lean'
CONTROLLER_ROOT_TEXT = ['import TlsMpc.Node.Main', 'def main := TlsMpc.Node.Main.main']
SESSION_DIR = 'TlsMpc/Node/Session'
SESSION_REF_ALLOWED = {'TlsMpc/Node/Session/State.lean', 'TlsMpc/Node/Session/Pool.lean', 'TlsMpc/Node/Session/Start.lean'}
SESSION_REF = re.compile(r'\b(IO\.Ref|IO\.mkRef|ST\.Ref|mkRef)\b')
# Stage S6: where the worker may be called directly, and `Opened` / own input made (check flow-calls).
# Stage S9 (STACK_NOTES J4): also the script implementations of the same flow functions: the script
# backends (Flows/*Backend.lean), the script runner (Flows/Runner.lean: op 93 through Legacy.call) and
# the selection (Flows/Select.lean). They make their `Opened` values with the same `Reveal.*` makers
# as the legacy implementations (no second set of makers in Reveal.lean).
FLOW_ALLOWED = re.compile(r'^TlsMpc/Node/Flows/(\w*Legacy|\w*Backend|Runner|Select)\.lean$'
                          r'|^TlsMpc/Node/(Secret|Reveal|Channels)\.lean$')
FLOW_SCOPE = re.compile(r'^handshake_backend/EmpHybridWork/PublicServiceController\.lean$|^TlsMpc/Node/')
FLOW_PATTERN = re.compile(
    r'\.(call|callArray|pipe|recording)\b'
    r'|\bTlsWorker\.(emptyReply|backend|applicationBackend|applicationSession|transport|applicationTransport|'
    r'waitingTransport|pollRecordLoop|awaitRecord|connect|connectVia|onConnection)\b'
    r'|\bTlsWorkerPipe\.code\b|\bLegacy\.(call|callArray|empty|inputOwn|handle)\b|\binputOwn\b'
    # (`KernelSpecs.Reveal.*`, the reveal kernel's specification, is another namespace: since S9 the
    # TLS proofs that use it are in the controller's closure through the script backends.)
    r'|(?<!KernelSpecs\.)\bReveal\.[a-z]\w*')
# Stage S5 (strict): files that may have no I/O site at all, whatever the baseline says: the
# controller and every module under TlsMpc/Node except the allowed ones.
STRICT_FILES = re.compile(r'^handshake_backend/EmpHybridWork/PublicServiceController\.lean$|^TlsMpc/Node/')


# ---- Lean source without comments and string literals (newlines kept, so lines still count).

def strip_lean(text):
    out, i, n = [], 0, len(text)
    while i < n:
        c = text[i]
        if text.startswith('--', i):
            j = text.find('\n', i)
            j = n if j < 0 else j
            i = j
        elif text.startswith('/-', i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith('/-', j):
                    depth, j = depth + 1, j + 2
                elif text.startswith('-/', j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            out.append(''.join(ch if ch == '\n' else ' ' for ch in text[i:j]))
            i = j
        elif c == 'r' and re.match(r'r#*"', text[i:i + 12]) and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_'.")):
            hashes = re.match(r'r(#*)"', text[i:]).group(1)
            end = text.find('"' + hashes, i + 2 + len(hashes))
            j = n if end < 0 else end + 1 + len(hashes)
            out.append(''.join(ch if ch == '\n' else ' ' for ch in text[i:j]))
            i = j
        elif c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == '\\' else 1
            j = min(j + 1, n)
            out.append('""' + ''.join('\n' for ch in text[i:j] if ch == '\n'))
            i = j
        elif c == "'" and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_'.")):
            m = re.match(r"'(\\x[0-9a-fA-F]{2}|\\u[0-9a-fA-F]{4}|\\.|[^'\\\n])'", text[i:i + 10])
            if m:
                out.append(' ' * len(m.group(0)))
                i += len(m.group(0))
            else:
                out.append(c)
                i += 1
        else:
            out.append(c)
            i += 1
    return ''.join(out)


_cache = {}


def source(rel):
    if rel not in _cache:
        with open(os.path.join(ROOT, rel), encoding='utf-8') as f:
            _cache[rel] = strip_lean(f.read())
    return _cache[rel]


def module_file(module):
    rel = module.replace('.', '/') + '.lean'
    return rel if os.path.isfile(os.path.join(ROOT, rel)) else None


IMPORT = re.compile(r'^\s*(?:public\s+|private\s+)?(?:meta\s+)?import\s+(?:all\s+)?(.*)$')


def imports(rel):
    found = []
    for line in source(rel).split('\n'):
        m = IMPORT.match(line)
        if m:
            found += [t for t in m.group(1).split() if re.match(r'^[A-Za-z_][\w.]*$', t)]
    return found


def closure(root_module):
    """Repository modules reachable from root_module (itself included): {module: file}."""
    seen, stack = {}, [root_module]
    while stack:
        module = stack.pop()
        if module in seen:
            continue
        rel = module_file(module)
        if rel is None:
            continue   # Lean, Std, Lake: outside the repository
        seen[module] = rel
        stack += imports(rel)
    return seen


def executables():
    with open(os.path.join(ROOT, 'lakefile.toml'), 'rb') as f:
        lake = tomllib.load(f)
    return {exe['name']: exe.get('root', exe['name']) for exe in lake.get('lean_exe', [])}


def line_of(text, index):
    return text.count('\n', 0, index) + 1


# ---- (a) I/O primitive sites.

IO_PATTERNS = [
    # IO.FS.* and IO.Process.* functions (a lower-case last component): readFile, withFile,
    # createDirAll, Handle.mk, output, spawn, run, exit, ... Types (Handle, Stdio, Mode) are not sites.
    (re.compile(r'\bIO\.(FS|Process)((?:\.[A-Z]\w*)*)\.([a-z]\w*)'), lambda m: f'IO.{m.group(1)}{m.group(2)}.{m.group(3)}'),
    (re.compile(r'\bIO\.(getEnv|println|eprintln|print|eprint|getStdout|getStderr|getStdin|setStdout|setStderr|setStdin|'
                r'getRandomBytes|rand|setRandSeed|sleep|monoMsNow|monoNanosNow|appPath|appDir|currentDir|getPID|getTID)\b'),
     lambda m: f'IO.{m.group(1)}'),
    (re.compile(r'\b(?:Std\.Time\.)?(Timestamp|PlainDateTime|ZonedDateTime|DateTime|PlainTime|PlainDate)\.now\b'),
     lambda m: f'Std.Time.{m.group(1)}.now'),
    (re.compile(r'(?<!IO\.FS)\.(pathExists|isDir|readDir|metadata|walkDir)\b'),
     lambda m: f'System.FilePath.{m.group(1)} (dot call)'),
]
IO_STDIO_VALUES = re.compile(r'^IO\.(FS\.Mode|Process\.Stdio)\.')
OPEN_IO = re.compile(r'^\s*open\b[^\n]*\b(IO(\.FS|\.Process)?|System\.FilePath|Std\.Time)\b(?!\.)', re.M)


QUALIFIER = re.compile(r'(?:^|[^\w.\'])([A-Z][\w\']*)$')


def io_sites(rel):
    text = source(rel)
    sites = []
    for pattern, name in IO_PATTERNS:
        for m in pattern.finditer(text):
            label = name(m)
            if IO_STDIO_VALUES.match(label):
                continue
            # `Namespace.metadata` (a function of a namespace, e.g. `Establish.metadata`) is not a
            # `System.FilePath` method called on a value: only dot calls on values count (S5).
            if label.endswith('(dot call)') and QUALIFIER.search(text[max(0, m.start() - 80):m.start()]):
                continue
            sites.append((label, line_of(text, m.start())))
    opens = [(m.group(0).strip(), line_of(text, m.start())) for m in OPEN_IO.finditer(text)]
    return sorted(sites, key=lambda s: s[1]), opens


def controller_files():
    exes = executables()
    return closure(exes[CONTROLLER_EXE])


def io_counts(files):
    counts, opens = {}, {}
    for rel in sorted(set(files.values())):
        sites, opened = io_sites(rel)
        per = {}
        for label, _ in sites:
            per[label] = per.get(label, 0) + 1
        if per:
            counts[rel] = dict(sorted(per.items()))
        if opened:
            opens[rel] = opened
    return counts, opens


def check_io(report):
    files = controller_files()
    counts, opens = io_counts(files)
    findings = []
    try:
        with open(BASELINE) as f:
            baseline = json.load(f)['sites']
    except FileNotFoundError:
        return [f'io-baseline: {os.path.relpath(BASELINE, ROOT)} is missing (run with --update-baseline once)'], {}
    lower = []
    for rel, per in counts.items():
        if rel in IO_ALLOWED:
            continue
        allowed = {} if STRICT_FILES.search(rel) else baseline.get(rel, {})
        for label, count in per.items():
            if count > allowed.get(label, 0):
                where = [line for l, line in io_sites(rel)[0] if l == label]
                findings.append(f'io-baseline: {rel}: {label} {count} sites, baseline {allowed.get(label, 0)} (lines {where[:12]})')
        for label, count in allowed.items():
            if per.get(label, 0) < count:
                lower.append(f'{rel}: {label} {per.get(label, 0)} < baseline {count}')
    for rel, entries in baseline.items():
        if STRICT_FILES.search(rel) and rel not in IO_ALLOWED:
            findings.append(f'io-baseline: {rel} is strict since S5 (no I/O site allowed); the baseline must not list it')
        elif rel not in counts and rel not in IO_ALLOWED:
            lower.append(f'{rel}: no sites now (baseline lists {sum(entries.values())})')
    # Stage S4: `Config.read` (TlsMpc/Node/Channels.lean) is the only reader of the environment.
    readers = [(rel, line) for rel in counts for label, line in io_sites(rel)[0] if label == 'IO.getEnv']
    if [rel for rel, _ in readers] not in ([], [CONFIG_READER]):
        findings.append(f'io-baseline: IO.getEnv must appear once, in Config.read ({CONFIG_READER}); found at {readers}')
    for rel, opened in opens.items():
        if rel not in IO_ALLOWED:
            for text, line in opened:
                findings.append(f'io-baseline: {rel}:{line}: `{text}` hides unprefixed I/O calls from this lint')
    info = dict(files=len(files), counts=counts, lower=lower)
    if report:
        total = sum(sum(per.values()) for per in counts.values())
        print(f'[io-baseline] controller closure: {len(files)} repository modules; {total} I/O sites in {len(counts)} files')
        by_label = {}
        for per in counts.values():
            for label, count in per.items():
                by_label[label] = by_label.get(label, 0) + count
        for rel, per in sorted(counts.items(), key=lambda kv: -sum(kv[1].values())):
            print(f'  {sum(per.values()):4}  {rel}')
        print('  by primitive:')
        for label, count in sorted(by_label.items(), key=lambda kv: -kv[1]):
            print(f'  {count:4}  {label}')
        if lower:
            print('  below the baseline (tighten with --update-baseline):')
            for line in lower:
                print('   ', line)
    return findings, info


def update_baseline():
    counts, _ = io_counts(controller_files())
    data = dict(
        about='I/O primitive sites per file of the controller\'s import closure (scripts/lint_node.py, check io-baseline). '
              'A count may only go down. Rewrite with --update-baseline after a stage moved sites into TlsMpc/Node/Channels.lean.',
        sites={rel: per for rel, per in counts.items() if rel not in IO_ALLOWED and not STRICT_FILES.search(rel)})
    with open(BASELINE, 'w') as f:
        f.write(json.dumps(data, indent=1, sort_keys=True) + '\n')
    print(f'wrote {os.path.relpath(BASELINE, ROOT)}: {sum(sum(p.values()) for p in data["sites"].values())} sites in {len(data["sites"])} files')


# ---- (b) Escape hatches.

HATCHES = re.compile(r'\b(sorry|admit|native_decide|bv_decide|ofReduceBool|implemented_by|extern|unsafe|opaque|axiom|csimp|'
                     r'skipKernelTC|partial\s+def)\b')


def hatches(rel):
    text = source(rel)
    return [(m.group(1), line_of(text, m.start())) for m in HATCHES.finditer(text)]


def lean_files(top):
    base = os.path.join(ROOT, top)
    out = []
    for dirpath, dirnames, filenames in os.walk(base):
        dirnames[:] = [d for d in dirnames if d not in ('.lake', 'Build', 'build', 'target', '.git')]
        out += [os.path.relpath(os.path.join(dirpath, f), ROOT) for f in filenames if f.endswith('.lean')]
    return sorted(out)


def check_hatches(report):
    findings = []
    for rel in lean_files(NODE_DIR):
        for word, line in hatches(rel):
            findings.append(f'escape-hatches: {rel}:{line}: `{word}`')
    if report:
        print(f'[escape-hatches] {NODE_DIR}: {len(lean_files(NODE_DIR))} files, {len(findings)} findings')
        # For information: the same patterns over the rest of the Lean tree (SECURITY_MAP C.6).
        tree = lean_files('TlsMpc') + lean_files('handshake_backend') + sorted(
            f for f in os.listdir(ROOT) if f.endswith('.lean'))
        per = {}
        for rel in tree:
            for word, line in hatches(rel):
                per.setdefault(word.split()[0] if word.startswith('partial') else word, []).append(f'{rel}:{line}')
        print(f'  whole tree, for information ({len(tree)} files in TlsMpc/, handshake_backend/, the root; not a failure):')
        for word, where in sorted(per.items()):
            print(f'  {len(where):4}  {word}: {", ".join(where[:6])}{" ..." if len(where) > 6 else ""}')
    return findings


# ---- (c) Emitter isolation.

def emitters():
    return {name: root for name, root in executables().items() if name.endswith('_emitter') or name == 'circuit_inventory'}


def check_emitters(report):
    findings = []
    lines = []
    for name, root in sorted(emitters().items()):
        mods = closure(root)
        bad = sorted(m for m in mods if m == 'TlsMpc.Node' or m.startswith('TlsMpc.Node.'))
        for m in bad:
            findings.append(f'emitter-isolation: {name} ({root}) imports {m}')
        lines.append(f'  {len(mods):4} modules  {name}' + ('   (imports the TlsMpc root module: anything added to it reaches this emitter)' if 'TlsMpc' in mods else ''))
    if report:
        print(f'[emitter-isolation] {len(lines)} emitters, {len(findings)} findings; each emitter\'s repository import closure:')
        print('\n'.join(lines))
    return findings


# ---- (d) Later stages.

def check_secret_val(report):
    findings = []
    for rel in lean_files('TlsMpc') + lean_files('handshake_backend'):
        if SECRET_ALLOWED.search(rel):
            continue
        text = source(rel)
        for m in re.finditer(r'\bSecret\.(val|mk)\b|\bexpose\b', text):
            findings.append(f'secret-val: {rel}:{line_of(text, m.start())}: `{m.group(0)}` outside the eliminators\' files')
    if report:
        print(f'[secret-val] {len(findings)} findings')
    return findings


def check_message_fields(report):
    rel = f'{NODE_DIR}/Messages.lean'
    if not os.path.isfile(os.path.join(ROOT, rel)):
        if report:
            print(f'[message-fields] {rel} does not exist yet')
        return []
    text = source(rel)
    findings = [f'message-fields: {rel}:{line_of(text, m.start())}: `{m.group(0)}`' for m in re.finditer(r'\b(Secret|Handle)\b', text)]
    if report:
        print(f'[message-fields] {len(findings)} findings')
    return findings


def check_flow_calls(report):
    findings = []
    files = sorted(rel for rel in set(controller_files().values()) if FLOW_SCOPE.search(rel))
    allowed_sites = 0
    for rel in files:
        text = source(rel)
        for m in FLOW_PATTERN.finditer(text):
            if FLOW_ALLOWED.search(rel):
                allowed_sites += 1
                continue
            findings.append(f'flow-calls: {rel}:{line_of(text, m.start())}: `{m.group(0)}` outside the legacy flow '
                            f'implementations (call the flow API, TlsMpc/Node/Flow.lean)')
    if report:
        print(f'[flow-calls] {len(files)} files (the controller and TlsMpc/Node in its closure); '
              f'{allowed_sites} sites in the allowed files; {len(findings)} findings')
    return findings


def check_session_state(report):
    findings = []
    root = os.path.join(ROOT, CONTROLLER_ROOT)
    if os.path.isfile(root):
        lines = [l.strip() for l in source(CONTROLLER_ROOT).split('\n') if l.strip()]
        if lines != CONTROLLER_ROOT_TEXT:
            findings.append(f'session-state: {CONTROLLER_ROOT} must be only {CONTROLLER_ROOT_TEXT} (comments aside); found {lines[:6]}')
    files = lean_files(SESSION_DIR) if os.path.isdir(os.path.join(ROOT, SESSION_DIR)) else []
    for rel in files:
        if rel in SESSION_REF_ALLOWED:
            continue
        text = source(rel)
        for m in SESSION_REF.finditer(text):
            findings.append(f'session-state: {rel}:{line_of(text, m.start())}: `{m.group(0)}` (session state is a field of '
                            f'Session.State, threaded explicitly)')
    if report:
        print(f'[session-state] controller root checked; {len(files)} session files; {len(findings)} findings')
    return findings


def check_ordering_sites(report):
    findings = []
    files = sorted(rel for rel in set(controller_files().values()) if FLOW_SCOPE.search(rel))
    sites = {name: [] for name in ORDERING_SITES}
    for rel in files:
        if rel in ORDERING_DEFINED:
            continue
        text = source(rel)
        for name in ORDERING_SITES:
            for m in re.finditer(re.escape(name) + r'\b', text):
                sites[name].append((rel, line_of(text, m.start())))
        for m in ORDERING_BARE.finditer(text):
            findings.append(f'ordering-sites: {rel}:{line_of(text, m.start())}: `{m.group(0)}` unqualified (write Flow.…, '
                            f'in the operations record only)')
        for m in ORDERING_OPEN.finditer(text):
            findings.append(f'ordering-sites: {rel}:{line_of(text, m.start())}: `{m.group(0).strip()}` hides flow calls '
                            f'from this check')
    for name, where in sites.items():
        if [rel for rel, _ in where] != [ORDERING_SITES[name]]:
            findings.append(f'ordering-sites: `{name}` must appear exactly once, in {ORDERING_SITES[name]} (its operations '
                            f'record); found at {where}')
    if report:
        print(f'[ordering-sites] {len(files)} files; sites: ' +
              ', '.join(f'{name} {where}' for name, where in sites.items()) + f'; {len(findings)} findings')
    return findings


def main():
    p = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    p.add_argument('--report', action='store_true')
    p.add_argument('--update-baseline', action='store_true')
    p.add_argument('--enable', default='', help='comma-separated checks to switch on in addition: ' + ', '.join(ALL_CHECKS))
    p.add_argument('--only', default='', help='comma-separated checks to run instead of the default ones')
    p.add_argument('--root', help='TEST: lint another tree (with its own lakefile.toml and scripts/lint_node_baseline.json)')
    a = p.parse_args()
    if a.root:
        global ROOT, BASELINE
        ROOT = os.path.abspath(a.root)
        BASELINE = os.path.join(ROOT, 'scripts', 'lint_node_baseline.json')
    if a.update_baseline:
        update_baseline()
        return
    checks = [c for c in (a.only.split(',') if a.only else DEFAULT_ON + [c for c in a.enable.split(',') if c]) if c]
    unknown = [c for c in checks if c not in ALL_CHECKS]
    if unknown:
        p.error(f'unknown checks: {unknown}')
    findings = []
    for check in ALL_CHECKS:
        if check not in checks:
            if a.report:
                print(f'[{check}] not switched on')
            continue
        if check == 'io-baseline':
            findings += check_io(a.report)[0]
        elif check == 'escape-hatches':
            findings += check_hatches(a.report)
        elif check == 'emitter-isolation':
            findings += check_emitters(a.report)
        elif check == 'secret-val':
            findings += check_secret_val(a.report)
        elif check == 'message-fields':
            findings += check_message_fields(a.report)
        elif check == 'flow-calls':
            findings += check_flow_calls(a.report)
        elif check == 'session-state':
            findings += check_session_state(a.report)
        elif check == 'ordering-sites':
            findings += check_ordering_sites(a.report)
    for line in findings:
        print('FAIL', line)
    print(f'lint_node: {len(findings)} findings ({", ".join(checks)})')
    sys.exit(1 if findings else 0)


if __name__ == '__main__':
    main()
