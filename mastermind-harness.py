#!/usr/bin/python3

# sample harness; your code should play against this code without
# any modification in this code. For any issues in this code
# please report asap.


# your code lives in this file; we will import it
import mastermind
import time
# We expect the following three functions in your code
# their usage will explain their interface.
#
#  mastermind.initialize(n,k)
#
#  mastermind.get_second_player_move()
#
#  mastermind.put_first_player_response( red, white )


# we randomly choose number of colors and length of sequence
import random
# n= random.randint(8, 12)
# k= random.randint(3, 7)
random.seed(time.time())
n = 4
k = 4
prob = 0
# two modes of testing
# play with self or play with a human
#
play_self = False
code = []

# pick a code in autoplay
if play_self:
    for i in range(k):
        code.append(random.randint(0, n-1))

# calculate response in auto play


def get_auto_response(move):
    assert(len(move) == k)
    reds = 0
    for i in range(k):
        if move[i] == code[i]:
            reds += 1
    matched_idxs = []
    whites_and_reds = 0
    for i in range(k):
        c = move[i]
        for j in range(k):
            if j in matched_idxs:
                continue
            if c == code[j]:
                whites_and_reds += 1
                matched_idxs.append(j)
                break

    # whites = whites_and_reds - reds

    if(random.uniform(0, 1) < prob and reds != k):
        whites_and_reds = random.randint(0, k)
        reds = random.randint(0, min(k-1, whites_and_reds))

    print("found a move:")
    print(move)
    print("Enter red count: " + str(reds))
    print("Enter white count: "+str(whites_and_reds - reds))
    return reds, whites_and_reds-reds


def get_human_response():
    red = int(input("Enter red count: "))
    white = int(input("Enter white count: "))
    if white+red > k:
        raise Exception("bad input!")
    return red, white


def play_game():
    if play_self:
        print("Chosen code:")
        print(code)
    # ~~~~ API CALL: We tell your code our choice of n and k
    #      n is the number of colors
    #      k is the size of the sequence
    #
    mastermind.initialize(n, k)
    # mastermind.printit()

    # print(mastermind.get_second_player_move())
    # print(mastermind.check_sum(11, 2))
    guess_list = []
    response_list = []
    red = 0
    while red < k:
        # ~~~~ API CALL: we collect your move
        # Your response should be of a list of k numbers. Ex. [ 2, 4, 4, 5]
        # The numbers indicate the colors
        #
        move = mastermind.get_second_player_move()
        guess_list.append(move)
        if play_self:
            red, white = get_auto_response(move)
        else:
            print("found a move:")
            print(move)
            red, white = get_human_response()
        # ~~~~ API CALL: We send you red and white responses
        #  red  : number of correct colors in correct positions
        #  white: number of correct colors in wrong positions
        #
        mastermind.put_first_player_response(red, white)
        # time.sleep(2)
    print("Game solved in " + str(len(guess_list)) +
          " moves for n = " + str(n) + " and k = " + str(k) + "!")


play_game()
