:- use_module(library(plunit)).

% task 3 d,a,b,d,d

delta(1,d,2).
delta(2,a,2).
delta(2,b,2).
delta(2,d,4).
delta(2,e,5).
delta(2,c,3).
delta(3,d,6).
delta(6,c,5).

start(1).

final(4).
final(5).

accept([],F) :- final(F).

accept([Single], S) :- 
    delta(S,Single,F),
    final(F).
    
accept([A,B|T], S) :-
    delta(S,A,F1),
    delta(F1,B,F2),
    accept(T, F2).

accept([A,B|T]) :-
    delta(S1,A,F1),
    start(S1),
    delta(F1,B,F2),
    accept(T, F2). 
% task 4

is_true(cst(true)).

is_true(and(X,Y)):-
    is_true(X),
    is_true(Y).

is_true(or(X,Y)):-
    is_true(X),
    is_true(Y).

is_true(or(X,Y)):-
    is_true(X),
    is_false(Y).

is_true(or(X,Y)):-
    is_false(X),
    is_true(Y).

is_true(not(X)) :- is_false(X).

is_false(cst(false)).

is_false(and(X,Y)) :-
    is_false(X);
    is_false(Y).

is_false(or(X,Y)) :-
    is_false(X),
    is_false(Y).

is_false(not(X)) :-
    is_true(X).

:- begin_tests(automaton).

test(accept,[nondet]) :-
    accept([d,a,b,a,b,b,b,c,d,c]).

test(accept2,[nondet]) :-
    accept([d,a,b,d]).

test(accept3,[nondet]) :-
    accept([d,e]).

test(accept4,[nondet]) :-
    accept([d,a,b,a,b,a,a,a,a,b,b,a,b,b,a,a,b,b,b,e]).

test(not_accept,[fail]) :-
    accept([d,a,b,a,e,d,c]).

test(not_accept2,[fail]) :-
    accept([d,a,b,d,d]).

test(not_accept3,[fail]) :-
    accept([d,a,b,a,b,a,a,a,b,b,a,a,b,b,c,b,e]).

:- end_tests(automaton).

:- begin_tests(sat).

test(sat, [nondet]) :-
    is_true(cst(true)).

test(sat2, [nondet]) :-
    is_true(not(cst(false))).

test(sat3, [nondet,true(A == false)]) :-
    is_true(not(cst(A))).

test(sat4, [nondet,true((A == true, B == false))]) :-
    is_true(and(cst(A), not(cst(B)))).

test(sat5_all, [nondet,all(A = [true])]) :-
    is_true(or(cst(A), not(cst(true)))).

test(sat6, [nondet]) :-
    is_true(or(not(and(cst(true),cst(false))),cst(false))).

test(sat7,[nondet]) :-
    is_true(or(not(and(cst(true),cst(false))),and(cst(true),or(cst(false),cst(true))))).

test(sat8, [nondet,true((A == false; B == true))]) :-
    is_true(or(not(and(cst(true),cst(A))),cst(B))).

test(sat9, [nondet,true((A == false, B == true))]) :-
    is_true(and(not(or(cst(false),cst(A))),cst(B))).

test(sat10_all, [nondet,all(B == [true])]) :-
    is_true(or(not(or(cst(false),cst(true))),cst(B))).

test(unsat,[fail]) :-
    is_true(not(cst(true))).

test(unsat2,[fail]) :-
    is_true(or(not(cst(true)),cst(false))).

test(unsat3,[fail]) :-
    is_true(and(not(cst(true)),or(cst(false),cst(true)))).

test(unsat4,[fail]) :-
    is_true(not(or(not(cst(true)),cst(true)))).

:- end_tests(sat).
