from z3 import *
import time

def find_minimal(graph, s, t):

    a = {} # adjacency list
    e = {} # propositional variables e[(i,j)] representing edges from i to j
    p = {} # propostional variables p[j] representing path from s to j
    
    t0 = time.time()
    for (i,j) in graph:
        if i in a.keys():
            a[i] += [j]
        else: 
            a[i] = [j]
            p[i] = Bool(f"p_{i}")

        if j in a.keys(): 
            a[j] += [i]
        else:
            a[j] = [i]
            p[j] = Bool(f"p_{j}")

        e[(i,j)] = Bool(f"e-{i}-{j}") 


    vs = [p[s]]
    
    # for i in a[s]:
        # vs += [Or(Not(e[(s,i)]), p[i])]

    for (i,j) in graph:
        vs += [Or(Not(p[i]), Not(e[(i,j)]), p[j])]
        vs += [Or(Not(p[j]), Not(e[(i,j)]), p[i])]

    vs += [Not(p[t])]

    # print(vs)
    sol = Optimize()
    sol.add(And(vs))
    # sol.maximize(Sum([If(e[edge],1,0) for edge in e.keys()]))

    for edge_c in e.keys():
        sol.add_soft(e[edge_c])

    sol.check()
    m = sol.model()

    ans = 0
    for edge_c in e.keys():
        if is_false(m[e[edge_c]]):
            ans+=1

    f0 = time.time()
    
    return ans
