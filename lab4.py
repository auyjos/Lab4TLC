#!/usr/bin/env python3
"""
Infix → (desugar + ?) → insertar '.' → Shunting-Yard (postfix) →
AST → AFN por Thompson → validación/renumeración → render árbol y AFN → simular AFN con w.

Uso:
    python shunting_yard_tree.py expresiones.txt [cadenas.txt]

Salidas por línea:
    tree_simplified_<i>.png    (AST)
    nfa_<i>.png                (AFN ya renumerado: start=1, accept=último)
    consola: 'sí' / 'no'
"""
import sys

from graphviz import Digraph


# ===================== Paso 0: desugar + y ? (recursivo) =====================
def expand_plus_question(expr: str) -> str:
    i, n, out = 0, len(expr), ""

    def is_escaped(pos):
        cnt, k = 0, pos - 1
        while k >= 0 and expr[k] == '\\':
            cnt += 1
            k -= 1
        return (cnt % 2) == 1

    while i < n:
        if expr[i] == '\\' and i + 1 < n:        # \X
            token = expr[i:i+2]; i += 2
        elif expr[i] == '(' and not is_escaped(i):  # ( ... )
            start, depth = i, 1
            i += 1
            while i < n and depth > 0:
                if expr[i] == '(' and not is_escaped(i): depth += 1
                elif expr[i] == ')' and not is_escaped(i): depth -= 1
                i += 1
            inner = expr[start+1:i-1]
            token = "(" + expand_plus_question(inner) + ")"
        else:                                     # literal
            token = expr[i]; i += 1

        if i < n and not is_escaped(i) and expr[i] in ['+', '?']:
            op = expr[i]; i += 1
            if op == '+':      out += token + token + '*'
            else:              out += f"({token}|ε)"
        else:
            out += token
    return out


# ===================== Paso 1: insertar concatenación explícita '.' =========
def insert_concatenation(expr: str):
    tokens, i = [], 0
    while i < len(expr):
        if expr[i] == '\\' and i + 1 < len(expr):
            tokens.append(expr[i:i+2]); i += 2
        else:
            tokens.append(expr[i]); i += 1

    result = []
    for j, tok in enumerate(tokens):
        if j > 0:
            prev = tokens[j-1]
            if prev not in ['|', '('] and tok not in ['|', ')', '*', '+', '?']:
                result.append('.')
        result.append(tok)
    return result


# ===================== Paso 2: Shunting-Yard (infix → postfix) ==============
def precedence(op: str):
    if op in ('*', '+', '?'): return 3
    if op == '.':             return 2
    if op == '|':             return 1
    return 0

def shunting_yard(tokens):
    output, stack, pasos = [], [], []
    for token in tokens:
        if token.startswith('\\') or (len(token) == 1 and (token.isalnum() or token in ['_', '[', ']', '{', '}', 'ε'])):
            output.append(token); pasos.append((f"operand {token}", output.copy(), stack.copy()))
        elif token == '(':
            stack.append(token); pasos.append(("push (", output.copy(), stack.copy()))
        elif token == ')':
            while stack and stack[-1] != '(':
                op = stack.pop(); output.append(op)
                pasos.append(("pop for )", output.copy(), stack.copy()))
            if stack and stack[-1] == '(':
                stack.pop(); pasos.append(("pop (", output.copy(), stack.copy()))
            else:
                pasos.append(("ignore unmatched )", output.copy(), stack.copy()))
        elif token in ['|', '.', '*', '+', '?']:
            while stack and precedence(stack[-1]) >= precedence(token):
                if stack[-1] == '(': break
                op = stack.pop(); output.append(op)
                pasos.append((f"pop op {op}", output.copy(), stack.copy()))
            stack.append(token); pasos.append((f"push op {token}", output.copy(), stack.copy()))
        else:
            pasos.append((f"ignore {token}", output.copy(), stack.copy()))
    while stack:
        op = stack.pop(); output.append(op)
        pasos.append((f"pop end {op}", output.copy(), stack.copy()))
    return output, pasos


# ===================== Paso 3: AST ==========================================
class RegexNode:
    def __init__(self, value, left=None, right=None):
        self.value, self.left, self.right = value, left, right

def build_syntax_tree(postfix_tokens):
    stack = []
    for tok in postfix_tokens:
        if tok in ('*', '+', '?'):
            child = stack.pop(); stack.append(RegexNode(tok, left=child))
        elif tok in ('.', '|'):
            r = stack.pop(); l = stack.pop()
            stack.append(RegexNode(tok, left=l, right=r))
        else:
            stack.append(RegexNode(tok))
    return stack.pop()


# ===================== Paso 4: Thompson (AST → AFN) =========================
class NFA:
    def __init__(self, start, accept, transitions):
        self.start = start            # int
        self.accept = accept          # int
        self.transitions = transitions# dict[int, list[(symbol, int)]]

def _merge_trans(tA, tB):
    for s, lst in tB.items():
        tA.setdefault(s, []).extend(lst)

def thompson_from_ast(root):
    counter = {'id': 0}
    def new_state():
        counter['id'] += 1
        return counter['id']

    def lit_symbol(tok):
        # '\X' → 'X'; 'ε' se queda como 'ε'
        if tok == 'ε': return 'ε'
        if tok.startswith('\\') and len(tok) == 2:
            return tok[1]
        return tok

    def build(node):
        if node.left is None and node.right is None:
            s, t = new_state(), new_state()
            sym = lit_symbol(node.value)
            trans = {s: [(sym, t)]}
            return NFA(s, t, trans)

        v = node.value
        if v == '.':   # concatenación
            A = build(node.left)
            B = build(node.right)
            _merge_trans(A.transitions, B.transitions)
            A.transitions.setdefault(A.accept, []).append(('ε', B.start))
            return NFA(A.start, B.accept, A.transitions)

        if v == '|':   # unión
            A = build(node.left)
            B = build(node.right)
            s, t = new_state(), new_state()
            trans = {}
            _merge_trans(trans, A.transitions)
            _merge_trans(trans, B.transitions)
            trans.setdefault(s, []).extend([('ε', A.start), ('ε', B.start)])
            trans.setdefault(A.accept, []).append(('ε', t))
            trans.setdefault(B.accept, []).append(('ε', t))
            return NFA(s, t, trans)

        if v == '*':   # estrella
            A = build(node.left)
            s, t = new_state(), new_state()
            trans = {}
            _merge_trans(trans, A.transitions)
            trans.setdefault(s, []).extend([('ε', A.start), ('ε', t)])
            trans.setdefault(A.accept, []).extend([('ε', A.start), ('ε', t)])
            return NFA(s, t, trans)

        if v == '+':   # por si no se desazucara (uno o más)
            # A . A*
            A = build(node.left)
            s1 = RegexNode('.', left=node.left, right=RegexNode('*', left=node.left))
            return build(s1)

        if v == '?':   # cero o uno
            A = build(node.left)
            s, t = new_state(), new_state()
            trans = {}
            _merge_trans(trans, A.transitions)
            trans.setdefault(s, []).extend([('ε', A.start), ('ε', t)])
            trans.setdefault(A.accept, []).append(('ε', t))
            return NFA(s, t, trans)

        raise ValueError(f"Operador no soportado: {v}")

    return build(root)


# ===================== Paso 5: simulación de AFN ============================
def epsilon_closure(states, transitions):
    stack = list(states)
    visited = set(states)
    while stack:
        s = stack.pop()
        for sym, t in transitions.get(s, []):
            if sym == 'ε' and t not in visited:
                visited.add(t); stack.append(t)
    return visited

def move(states, sym, transitions):
    out = set()
    for s in states:
        for a, t in transitions.get(s, []):
            if a == sym:
                out.add(t)
    return out

def simulate_nfa(nfa: NFA, w: str) -> bool:
    if w == 'ε':  # permitir 'ε' como cadena vacía
        w = ''
    cur = epsilon_closure({nfa.start}, nfa.transitions)
    for ch in w:
        cur = epsilon_closure(move(cur, ch, nfa.transitions), nfa.transitions)
        if not cur:
            break
    cur = epsilon_closure(cur, nfa.transitions)
    return nfa.accept in cur


# ===================== Validación y renumeración =============================
def _collect_states(transitions):
    states = set(transitions.keys())
    for lst in transitions.values():
        for _, t in lst:
            states.add(t)
    return states

def validate_nfa(nfa: NFA):
    """
    Devuelve lista de strings con advertencias/errores.
    (No detiene ejecución; imprime en consola en la orquestación).
    """
    issues = []
    T = nfa.transitions
    states = _collect_states(T)

    # 1) start/accept presentes
    if nfa.start not in states:
        issues.append(f"El estado inicial {nfa.start} no aparece en transiciones.")
    if nfa.accept not in states:
        issues.append(f"El estado de aceptación {nfa.accept} no aparece en transiciones.")

    # 2) grados
    indeg = {s: 0 for s in states}
    outdeg = {s: 0 for s in states}
    for s, lst in T.items():
        outdeg[s] += len(lst)
        for _, t in lst:
            indeg[t] = indeg.get(t, 0) + 1
    if indeg.get(nfa.start, 0) != 0:
        issues.append(f"El estado inicial {nfa.start} tiene indegree={indeg.get(nfa.start, 0)} (esperado 0).")
    if outdeg.get(nfa.accept, 0) != 0:
        issues.append(f"El estado de aceptación {nfa.accept} tiene outdegree={outdeg.get(nfa.accept, 0)} (esperado 0).")

    # 3) alcanzabilidad desde start
    from collections import deque
    q = deque([nfa.start])
    seen = {nfa.start}
    while q:
        s = q.popleft()
        for _, t in T.get(s, []):
            if t not in seen:
                seen.add(t); q.append(t)
    unreachable = states - seen
    if unreachable:
        issues.append(f"Hay estados inalcanzables desde {nfa.start}: {sorted(unreachable)}")

    # 4) accept alcanzable
    if nfa.accept not in seen:
        issues.append(f"El estado de aceptación {nfa.accept} NO es alcanzable desde {nfa.start}.")

    return issues

def renumber_nfa(nfa: NFA, make_accept_last: bool = True) -> NFA:
    """
    Renumera estados con BFS desde start para que:
      - start -> 1
      - (opcional) accept -> último
    Mantiene la estructura del AFN.
    """
    from collections import deque

    T = nfa.transitions
    states = _collect_states(T)

    # Orden BFS desde start (para layout natural)
    q = deque([nfa.start])
    seen = {nfa.start}
    order = []
    while q:
        s = q.popleft()
        order.append(s)
        # orden determinista por estética (símbolo, destino)
        for sym, t in sorted(T.get(s, []), key=lambda x: (x[0], x[1])):
            if t not in seen:
                seen.add(t); q.append(t)

    # Si hubiera estados aislados, añadirlos al final
    for s in sorted(states):
        if s not in seen:
            order.append(s)

    # Forzar accept al final si se pide
    if make_accept_last and nfa.accept in order:
        order = [s for s in order if s != nfa.accept] + [nfa.accept]

    mapping = {old: i+1 for i, old in enumerate(order)}

    T2 = {}
    for s, lst in T.items():
        ns = mapping[s]
        for sym, t in lst:
            T2.setdefault(ns, []).append((sym, mapping[t]))

    return NFA(start=mapping[nfa.start], accept=mapping[nfa.accept], transitions=T2)


# ===================== Render: Árbol y AFN ==================================
def visualize_tree(root, filename='tree'):
    dot = Digraph(format='png')
    dot.attr(rankdir='TB')  # raíz arriba, hojas abajo
    cnt = 0
    def visit(node):
        nonlocal cnt
        nid = f"n{cnt}"; cnt += 1
        dot.node(nid, label=node.value)
        if node.left:
            lid = visit(node.left); dot.edge(lid, nid)   # hijo → padre
        if node.right:
            rid = visit(node.right); dot.edge(rid, nid)  # hijo → padre
        return nid
    visit(root)
    dot.render(filename, cleanup=True)

def visualize_nfa(nfa: NFA, filename='nfa'):
    dot = Digraph(format='png')
    dot.attr(rankdir='LR')
    # nodos
    states = _collect_states(nfa.transitions)
    for s in states:
        shape = 'doublecircle' if s == nfa.accept else 'circle'
        dot.node(str(s), shape=shape)
    # flecha de inicio
    dot.node('start', shape='point')
    dot.edge('start', str(nfa.start))
    # transiciones
    for s, lst in nfa.transitions.items():
        for sym, t in lst:
            label = sym if sym != ' ' else '␠'
            dot.edge(str(s), str(t), label=label)
    dot.render(filename, cleanup=True)


# ===================== Orquestación =========================================
def procesar_archivo(regex_path, strings_path=None):
    strings = None
    if strings_path:
        with open(strings_path, encoding='utf-8') as g:
            strings = [line.rstrip('\n') for line in g]

    with open(regex_path, encoding='utf-8') as f:
        idx = 1
        for k, linea in enumerate(f):
            expr = linea.strip()
            if not expr or expr.startswith('#'):
                continue

            # Parseo: desugar → concat → postfix → AST
            expr2 = expand_plus_question(expr)
            tokens = insert_concatenation(expr2)
            postfix, _ = shunting_yard(tokens)
            root = build_syntax_tree(postfix)

            # Visualización del AST
            visualize_tree(root, filename=f"tree_simplified_{idx}")

            # Thompson → NFA (lógico)
            nfa = thompson_from_ast(root)

            # Validaciones + renumeración (start=1, accept=último)
            issues = validate_nfa(nfa)
            if issues:
                print("Validaciones del AFN:")
                for msg in issues:
                    print("  -", msg)
            nfa = renumber_nfa(nfa, make_accept_last=True)

            # Visualización del NFA renumerado
            visualize_nfa(nfa, filename=f"nfa_{idx}")

            # Obtener w
            if strings is not None and k < len(strings):
                w = strings[k]
            else:
                w = input(f"w para la expresión {idx} ('{expr}'): ").strip()

            # Simular
            ok = simulate_nfa(nfa, w)
            print(f"\n=== Expr #{idx} ===")
            print(f"r (infijo)    : {expr}")
            print(f"r (expandido) : {expr2}")
            print(f"postfix       : {''.join(postfix)}")
            print(f"w             : {w!r}")
            print("¿w ∈ L(r)?    :", "sí" if ok else "no")
            print(f"Árbol: tree_simplified_{idx}.png | AFN: nfa_{idx}.png\n")
            idx += 1


# ===================== main ==================================================
if __name__ == '__main__':
    if len(sys.argv) not in (2, 3):
        print("Uso: python shunting_yard_tree.py <expresiones.txt> [cadenas.txt]")
        sys.exit(1)
    regex_path = sys.argv[1]
    strings_path = sys.argv[2] if len(sys.argv) == 3 else None
    procesar_archivo(regex_path, strings_path)
