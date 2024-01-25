:- use_module(library(plunit)).

% task 2

loves(siegfried,krimhild).
loves(krimhild,siegfried).
loves(gunther,brunhild).
likes(siegfried,gunther).
likes(gunther,krimhild).
likes(gunther,hagen).
likes(brunhild,X):-
    hates(X,siegfried).
hates(krimhild,brunhild).
hates(brunhild,siegfried).
hates(brunhild,gunther).
hates(brunhild,krimhild).
hates(hagen,siegfried).
hates(hagen,X) :-
    loves(X, siegfried).
hates(alberich, X) :- X \= alberich.

% task 4

% last_but_one(+L, -E).

last_but_one([X,Y],X).
last_but_one([_|List], E) :- last_but_one(List, E).

% my_infix(+I, +L).

my_infix(I,L) :-
    append(_, S, L), % all possible suffixes (teillisten)
    append(I, _, S), % check if any suffix equal the infix: anypart of the list that is the same
    I \= []. % Infix not empty.
    % append succeeds if C is the result of appending append(A,B,C) -> B to A.
    % and Variables go for any Output


% my_suffix(+I, +L).

my_suffix(S,L) :-
    append(_, S, L),
    S \= [].

% my_prefix(+I, +L).

my_prefix(P, L) :- 
    append(P, _, L),
    P \= [].

% del_element(+E, +L, -R).


del_element(_, [],[]).
del_element(X, [X | T],R) :-
    del_element(X, T , R).
del_element(X, [H | T], [H | R]) :-
    X \= H,
    del_element(X, T, R).

% task 5

% insert_at(+E, +L, +Index, -NL).

insert_at(E, [], Index, [E]) :- Index >= 1.
insert_at(E, L, 1, [E|L]).

insert_at(E, [P|L], Index, [P|NL]) :-
    Index > 1,
    NewIndex is Index - 1,
    insert_at(E, L, NewIndex, NL).


% Run all tests:
%   run_tests.
% Run all tests in a block:
%   run_tests(lists).
% Run a single test in a block:
%   run_tests(lists:is_a_list).
:- begin_tests(lists).

test(last_but_one, [nondet,true(L == c)]) :-
    last_but_one([a,b,c,d], L).

test(last_but_one_fail, [fail]) :-
    last_but_one([a], _).

test(last_but_one_fail2, [fail]) :-
    last_but_one([], _).

test(last_but_one_all, [all(L == [d])]) :-
    last_but_one([a,b,c,d,e], L).

test(infix_empty, [fail,nondet]) :-
    my_infix([], [a,b,c,d]).

test(infix1, [nondet]) :-
    my_infix([a,b,c,d], [a,b,c,d]).

test(infix2, [nondet]) :-
    my_infix([b,c], [a,b,c,d]).

test(infix3, [nondet]) :-
    my_infix([a,b,c], [a,b,c,d]).

test(infix4, [nondet]) :-
    my_infix([c,d], [a,b,c,d]).

test(infix_full, [nondet]) :-
    my_infix([a,b,c,d], [a,b,c,d]).

test(infix_fail, [fail,nondet]) :-
    my_infix([p,r,o,l,o,g], [a,b,c,d]).

test(suffix_empty, [fail,nondet]) :-
    my_suffix([], [a,b,c,d]).

test(suffix1, [nondet]) :-
    my_suffix([a,b,c,d], [a,b,c,d]).

test(suffix2, [nondet]) :-
    my_suffix([c,d], [a,b,c,d]).

test(suffix_fail, [fail,nondet]) :-
    my_suffix([a,b], [a,b,c,d]).

test(suffix_full, [nondet]) :-
    my_suffix([a,b,c,d], [a,b,c,d]).

test(prefix_empty, [fail,nondet]) :-
    my_prefix([], [a,b,c,d]).

test(prefix1, [nondet]) :-
    my_prefix([a,b,c,d], [a,b,c,d]).

test(prefix2, [nondet]) :-
    my_prefix([a,b], [a,b,c,d]).

test(prefix_fail1, [fail,nondet]) :-
    my_prefix([b,c], [a,b,c,d]).

test(prefix_full, [nondet]) :-
    my_prefix([a,b,c,d], [a,b,c,d]).

test(del_element, [nondet,true(R == [b,c,d])]) :-
    del_element(a,[a,b,c,d],R).

test(del_element_all, [all(R == [[b,c,d]])]) :-
    % evaluates all choicepoints
    del_element(a,[a,b,c,d],R).

test(del_element_twice, [nondet,true(R == [b,c,d])]) :-
    del_element(a, [a,b,c,d,a], R).

test(del_element_twice_failing, [fail]) :-
    del_element(a, [a,b,c,d,a], R), !, R == [b,c,d,a].

:- end_tests(lists).

:- begin_tests(insert_at).

test(insert_at,[nondet,true(R == [a,test,b,c])]) :-
    insert_at(test, [a,b,c], 2, R).

test(insert_at2,[nondet,true(R == [k,a,b])]) :-
    insert_at(k, [a,b], 1, R).

test(insert_at3,[nondet,true(R == [a,d])]) :-
    insert_at(d, [a], 3, R).

test(insert_at4,[nondet,true(R == [p])]) :-
    insert_at(p, [], 3, R).

test(insert_at5,[fail,nondet]) :-
    insert_at(a, [a,b,c], -3, _).

test(insert_at_all,[nondet,all(R == [[a,b,p,c,d,e]])]) :-
    % evaluates all choicepoints
    insert_at(p, [a,b,c,d,e], 3, R).

:- end_tests(insert_at).