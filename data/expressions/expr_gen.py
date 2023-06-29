import random
import sys
import copy

expressions_folder = ""
atoms = [":a", ":b", ":c", ":d", ":e", ":f", ":g", ":h", ":i"] # ",:true", ":false"]
atoms = atoms + ["{:not, "+ x +"}" for x in atoms]
predicates_un = [":F", ":G", ":H"]
predicates_bin = [":I", ":J"]
atoms_pred = atoms
for p in predicates_un:
    new_preds = ["{" + p +", [" + x + "]}" for x in atoms]
    random.shuffle(new_preds)
    atoms_pred = atoms_pred + new_preds[:3]
for p in predicates_bin:
    atoms2 = copy.deepcopy(atoms)
    random.shuffle(atoms2)
    new_preds = ["{" + p +", [" + x + ", " + y + "]}" for x, y in zip(atoms, atoms2)]
    random.shuffle(new_preds)
    atoms_pred =  atoms_pred + new_preds[:3]
operators = {":not": (1, 1),
             ":and": (2, 6),
            # ":nand": 2,
             ":or": (2, 6),
            # ":nor": 2,
            # ":rimp": 2,
            # ":nrimp": 2,
            # ":limp": 2,
            # ":nlimp": 2
             }

def generate_expression(atoms, operators, depth):
    if depth == 0:
        return atoms[random.randint(0, len(atoms) - 1)]
    else:
        op = list(operators.keys())[random.randint(0, len(operators.keys()) - 1)]
        op_arity = operators[op]
        n_arguments = random.randint(op_arity[0], op_arity[1])
        if op == ":not":
            argument = generate_expression(atoms, operators, depth-1)
            return f'{{{op}, {argument}}}'
        else:
            expression = f'{{{op}, ['
            for i in range(n_arguments):
                argument = generate_expression(atoms, operators, depth-1)
                if i == 0:
                    expression = f'{expression}{argument}'  
                elif i == n_arguments -1 :
                    expression = f'{expression}, {argument}]}}'
                else:
                    expression = f'{expression}, {argument}'
            return expression


n = int(sys.argv[1])
d = int(sys.argv[2])
nodes = pow(3, d) - 1
out_path = expressions_folder + "n" + str(n) + "d" + str(d) + "_nodes" + str(nodes) + ".txt"

with open(out_path, "w") as res:
    for i in range(n):
        print(str(i) + "/" + str(n))
        print(f"generating expression with on avg. {nodes} nodes..")
        print(atoms_pred)
        expr = generate_expression(atoms_pred, operators, d)
        print("writing to file..")
        res.write(expr)
        if i != n-1:
            res.write("\n")
        print("done.")