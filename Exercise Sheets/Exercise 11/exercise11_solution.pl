:- use_module(library(plunit)).


% Task 2

:- dynamic tier/1.

% test
%tier_h(X) :-
%    assertz(tier(taube)),
%    assertz(tier(adler)),
%    tier(X).

btasserta(Assertion) :- asserta(Assertion).
btasserta(Assertion) :- retract(Assertion), !, fail.

%btretract(Assertion) :- (Assertion ->
%                        was_asserted = true; was_asserted = false),
%                        retract(Assertion),
%                        (was_asserted = true -> asserta(Assertion); true).

btretract(Assertion) :- retract(Assertion). 
btretract(Assertion) :- btasserta(Assertion), !, fail. % Does not completely work, for instance when a fact was not true, then it is asserted


%btasserta(Assertion) :- (Assertion -> (retract(Assertion), fail); asserta(Assertion)).
%btretract(Assertion) :- (Assertion -> (retract(Assertion)); (asserta(Assertion), fail)).



% Task 3

mysum(L, R) :- mysum_acc(L, 0, R).

mysum_acc([], Acc, Acc).
mysum_acc([H|T], Acc, R) :-
    NewAcc is Acc + H,
    mysum_acc(T, NewAcc, R).

mysum_st([], 0).
mysum_st([H|T], R) :-
    mysum_st(T, TR),
    R is TR + H.


% Task 4

reduce(P, [H|T], R) :- reduce(P, T, H, R).


%reduce(_, [Acc], R) :- !, R = Acc.
%reduce(P, [Acc,H|T], Res) :-
%    call(P, Acc, H, NewAcc),
%    reduce(P, [NewAcc|T], Res).

% with four arguments

reduce(_, [], Acc, R) :- !, R = Acc.
reduce(P, [H|T], Acc, Res) :-
    call(P, Acc, H, NewAcc),
    reduce(P, T, NewAcc, Res).


% Task 5

interleave([], R) :- !, R = [].
interleave(L, R) :-
    !, interleave_acc(L, [], R).

interleave_acc(L, Acc, R) :-
    member([], L), !,
    R = Acc.

interleave_acc(L, Acc, R) :-
    maplist(first(), L, First, Rest),
    append(Acc, First, NewAcc),
    interleave_acc(Rest, NewAcc, R).

first([H|T], H, T).


:- begin_tests(mysum).

test(sum1, [true(S == 0)]) :-
    mysum([], S).

test(sum2, [true(S == 6)]) :-
    mysum([1,2,3], S).

test(sum3, [true(S == 15)]) :-
    mysum([1,2,3,4,5], S).

test(sum_all1, [all(S == [15])]) :-
    mysum([1,2,3,4,5], S).

test(sum_all2, [all(S == [0])]) :-
    mysum([], S).

:- end_tests(mysum).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% used for the "higher_order" tests
add(Cst, Val, Sum) :- Sum is Val + Cst.

:- begin_tests(higher_order).

test(reduce1, [fail]) :-
    reduce(add, [], _).

test(reduce2, [true(R == 6)]) :-
    reduce(add, [1,2,3], R).

test(reduce3, [true(R == 1)]) :-
    reduce(add, [1], R).

:- end_tests(higher_order).

:- begin_tests(interleave).

test(interleave1, [true(L == [a, 1, b, 2])]) :-
    interleave([[a,b],[1,2]], L).

test(interleave2, [true(L == [a, 1, x, b, 2, y, c, 3, z])]) :-
    interleave([[a,b,c],[1,2,3],[x,y,z]], L).

test(interleave3, [true(L == [])]) :-
    interleave([], L).

test(interleave4, [true(L == [1,3])]) :-
    interleave([[1,2],[3]], L).

test(interleave_all1, [all(L == [[a, 1, b, 2]])]) :-
    interleave([[a,b],[1,2]], L).

test(interleave_all2, [all(L == [[1,3]])]) :-
    interleave([[1,2],[3]], L).

:- end_tests(interleave).