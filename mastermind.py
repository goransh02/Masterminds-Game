from z3.z3 import *
########## To keep track of the propositional variables #########

var_counter = 0     # global propostional variable(PV) counter


def count():
    global var_counter
    count = var_counter
    var_counter = var_counter + 1
    return str(count)

# this function supplies a unique PV on each call


def get_fresh_bool(suff=""):
    return Bool("b_" + count() + "_" + suff)

# this function supplies a vector of unique PVs


def get_fresh_vec(length, suff=""):
    n_vs = []
    for _ in range(length):
        n_vs.append(get_fresh_bool(suff))
    return n_vs

#################### Helper functions ##########################

# returns list of clauses for sum of input *vars* to be atleast *k*


def at_most(vars, k):
    clauses = []
    if(k == 0):
        return [Not(pi) for pi in vars]
    if(k == len(vars)):
        return clauses

    s = [get_fresh_vec(k) for _ in range(len(vars))]

    # for p1
    clauses += [Or(Not(vars[0]), s[0][0])]
    clauses += [Not(s[0][i]) for i in range(1, k)]

    # for pi; where i \in {1,2,...,n}
    for i in range(1, len(vars)):
        clauses += [Or(Not(Or(vars[i], s[i-1][0])), s[i][0])]
        for j in range(1, k):
            clauses += [Or(Not(Or(And(vars[i], s[i-1][j-1]), s[i-1][j])), s[i][j])]

    # additional
    for i in range(1, len(vars)):
        clauses += [Or(Not(s[i-1][k-1]), Not(vars[i]))]

    return clauses

# returns list of clauses for the sum of input *vars* to be exactly *k*


def sum_k(vars, k):
    clauses = []
    nvars = [Not(var) for var in vars]

    # sum atleast k
    clauses += at_most(vars, k)

    # sum atmost k
    clauses += at_most(nvars, len(vars)-k)

    return clauses


######################## API ###########################
'''
We proceed in 2 steps:

1) We check which colors are actually present in the array of player1 by querying with arrays of same color at each position. As ideally in the true case, this would mean we get non-zero reds and zero whites for actually present colors and both zero for colors not present. So, after iterating over all colors when we get some of reds equal to k then we proceed to next step.

Also, we have propositional variables pvs[i][j] representing whether we have color 'i' at the 'j'th position or not. So, after this step we will update the clauses as this step gives us which color occurs how many times, so we get sum constraints over colors. And we already had sum_i pvs[i][j] = 1 for all j.

2) Then we sequentially output the satisfying models to player1 and according to the number of reds output by the player we get more constraints. If the player lies, then the set of clauses become UNSAT and we get back to original clauses that we had after step1. If the formula becomes UNSAT for more than some set THRESH values then we reset and check for colors again. Otherwise, we will get our correct sequence. 

'''

# STATIC VARIABLES

# parameters required for dealing with the cases when player1 lies
THRESH = 20
TRUE_THRESH_1 = 1
TRUE_THRESH_2 = 1

n = k = 0       # initialising n, k to 0
moves = []      # this list stores all the moves in sequence

clauses_outs = {}       # dictionary to store the response from player1 on the same move

# For Step 1
colors_present = []     # this list stores colors actually present in the player1 array
color = 0               # current color in the first step of checking
# bool deciding whether we are on first step or second step of guessing
find_colors = True

# For Step 2
pvs = []                # propositional variables
clauses = []            # set of clauses
# mapping of original colors to new list which contains list of colors that are actually present
org_to_sel = {}
unsat_count = 0         # numer of times set of clauses have become unsat
# if we have same ouputs on the same move for more than some TRUE_THRESH_i times than we can say the player1 hasn't lied
essential_clauses_count = 0
# these are those clauses of which we are pretty certain of being true
almost_true_clauses = []

# Variables to assert/check/gauge the algorithm (output(moves) of any API function doesn't depend on these)
r_count = 0
color_moves = 1


def initialize(num, sel):
    global n, k, moves
    n = num
    k = sel
    moves = []
    guess = [0]*k   # first move, all zeros

    moves.append(guess)


def get_second_player_move():
    global n, k, moves

    # our move is always the last element in the *moves* array
    return moves[len(moves)-1]


def put_first_player_response(red, white):
    global var_counter, n, k, moves, colors_present, find_colors, color, clauses, org_to_sel, pvs, unsat_count, essential_clauses_count, r_count, almost_true_clauses, THRESH, TRUE_THRESH_1, TRUE_THRESH_2, color_moves

    # if reds is same as k, we have our solution
    if(red == k):
        return

    # Step 1
    if (find_colors and red > 0 and white == 0):
        key = str(moves[len(moves)-1])

        # Modelling lies: only if the same move have same ouputs more than some TRUE_THRESH_i times then we consider the ouput to be true
        ess = False
        if key in clauses_outs.keys():
            if clauses_outs[key] == True:
                pass
            elif clauses_outs[key].count(red) >= TRUE_THRESH_2:
                ess = True
                clauses_outs[key] = True
            else:
                clauses_outs[key] += [red]

        else:
            clauses_outs[key] = [red]

        # we can add potentially true outputs to get set of color clauses
        if ess:
            colors_present.append((color, red))
            org_to_sel[color] = len(colors_present)-1

            total_ele = sum(list(map(lambda x: x[1], colors_present)))

            # if sum of occurences of colors becomes k then we can proceed to Step2 after adding the learned color, position clauses
            if(total_ele == k):
                find_colors = False

                pvs = [get_fresh_vec(k) for _ in range(len(colors_present))]

                # sum over positions for all colors as we get from player1
                for i in range(len(colors_present)):
                    clauses += sum_k(pvs[i], colors_present[i][1])

                # sum over colors for all positions is 1
                for j in range(k):
                    list_pvs = []
                    for i in range(len(colors_present)):
                        list_pvs += [pvs[i][j]]
                    clauses += sum_k(list_pvs, 1)

                # we term these clauses as essential clauses
                essential_clauses_count = len(clauses)

                # get a satisfying assignment for our current set of clauses and proceed to step2 from next response onwards
                sol = Solver()
                sol.add(And(clauses))
                assert(sol.check() == sat)
                moves.append(get_move(sol.model()))

                return

            elif (total_ele > k):
                r_count += 1
                # reset(i.e. check for colors again) as this implies we were lied about many inputs
                reset()

        # if we haven't checked the output enough times
        else:
            color = (color-1) % n

    # for checking next color
    if(find_colors):
        color = (color+1) % n
        moves.append([color]*k)
        color_moves += 1

    # Step 2
    else:
        # moves will contain colors from original set
        # pvs in last move

        # again to check the correctness of any ouput so as to add corresponding clauses as permanent clauses we have to check over multple responses of the same move
        ess = False
        key = str(moves[len(moves)-1])

        if key in clauses_outs.keys():
            if clauses_outs[key] == True:
                pass
            elif clauses_outs[key].count((red, white)) >= TRUE_THRESH_1:
                ess = True
                clauses_outs[key] = True
            else:
                clauses_outs[key] += [(red, white)]

        else:
            clauses_outs[key] = [(red, white)]

        # invariant after step1, if not satisfied then there was a lie somewhere
        if(red+white != k):
            unsat_count += 1

        # adding clause corresponding to the current response, this is a temporary clause these can be removed in case they make formula UNSAT
        sol = Solver()
        selected_pvs = []
        for i in range(k):
            last_move = moves[len(moves)-1]
            selected_pvs += [pvs[org_to_sel[last_move[i]]][i]]

        new = sum_k(selected_pvs, red)
        clauses += new

        # if ess is set, then the new clauses are not temporary. They were not because of a lie with high porbability
        if ess:
            almost_true_clauses += new

        sol.add(And(clauses))

        # if UNSAT
        if(sol.check() == unsat):
            # UNSAT count greater than some specified threshold then we reset to  Step 1
            if(unsat_count >= THRESH):
                moves.append([0]*k)
                reset()
            # otherwise we remove the temporary clauses and again continue in the Step 2
            else:
                clauses = clauses[:essential_clauses_count]
                clauses += almost_true_clauses
                unsat_count += 1
                sol = Solver()
                sol.add(And(clauses))

                # assert(sol.check() == sat)
                if(sol.check() == unsat):
                    moves.append([0]*k)
                    reset()
                else:
                    moves.append(get_move(sol.model()))

        # if SAT, then we append a satisfying move to current moves
        else:
            moves.append(get_move(sol.model()))


# getting the move in the form of array from the satisfying model of current clauses
def get_move(model):
    global k, colors_present, pvs

    move = [0]*k
    for i in range(len(colors_present)):
        for j in range(k):
            if is_true(model[pvs[i][j]]):
                # print("here")
                move[j] = colors_present[i][0]

    return move


# to reset all the global variables in the case of many lies leading to unsat set of clauses
def reset():
    global var_counter, n, k, moves, colors_present, find_colors, color, clauses, org_to_sel, pvs, unsat_count, essential_clauses_count, almost_true_clauses, clauses_outs

    print("reset")
    var_counter = 0
    clauses = []
    color = 0
    find_colors = True
    unsat_count = 0
    org_to_sel = {}
    colors_present = []
    essential_clauses_count = 0

    almost_true_clauses = []
    clauses_outs = {}


####################### Testing funcitons ##########################

# just to check the ouput of the function sum_k
def check_sum(n, k):
    p = get_fresh_vec(n)

    # notp = [Not(pi) for pi in p]
    vars = sum_k(p, k)
    # vars += at_most(notp, n-k)

    sol = Solver()
    sol.add(And(vars))

    if sat == sol.check():
        m = sol.model()
        for pi in p:
            print(pi, m[pi])


def print_model(model):
    global pvs, n, k, colors_present

    for i in range(len(colors_present)):
        for j in range(k):
            print(model[pvs[i][j]])
        print("")
