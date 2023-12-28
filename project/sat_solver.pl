:- module(sat_solver,[normalise/2, to_cnf/2, solve/1]).

:- load_test_files([]).

%% normalise(+Formula, -NFormula).
%% basecase

normalise(lit(X), X) 
    :-!.

normalise(not(and(X,Y)), Norm)
    :- !, normalise(or(not(X),not(Y)), Norm).

normalise(not(or(X,Y)), Norm)
    :- !, normalise(and(not(X),not(Y)), Norm).

normalise(not(not(X)), NormalisedX) 
    :- !, normalise(X, NormalisedX).    

%% negation
normalise(not(X), not(NX)) 
    :- !, normalise(X,NX).

%% conjunction
normalise(and(X,Y), and(NX,NY)) 
    :- !, normalise(X,NX), normalise(Y,NY).

%% disjunction
normalise(or(X, Y), or(NX, NY)) 
    :- !, normalise(X, NX), normalise(Y, NY).

%% implication
normalise(implies(X, Y), or(NX, NY)) 
    :- !, normalise(not(X), NX), normalise(Y, NY).

%% equivalence
normalise(equivalence(X, Y), and(NX, NY)) 
    :- !, normalise(implies(X,Y), NX),
       normalise(implies(Y,X), NY).

%% min_one_pos
normalise(min_one_pos(Vars), NormalisedForm)
    :- list_to_disjunction(Vars,Disjunction),
        normalise(Disjunction, NormalisedForm).

%% exactly_one_pos
normalise(exactly_one_pos(Literals), NormalisedForm) :-
    findall(OrClause, pairwise_negation(Literals, OrClause), PairwiseNegations),
    list_to_disjunction(Literals, AtLeastOne),
    append(PairwiseNegations, [AtLeastOne], AllClauses),
    list_to_conjunction(AllClauses, Conjunctionss),
    normalise(Conjunctionss, NormalisedForm).

%% Create pairwise negation clauses
pairwise_negation(Literals, OrClause) :-
    select(Lit1, Literals, Remaining),
    member(Lit2, Remaining),
    Lit1 @< Lit2,
    OrClause = or(not(Lit1), not(Lit2)).

% Helper
negate(X, NX) 
    :- !, normalise(not(lit(X)), NX).

list_to_conjunction([X], X).
list_to_conjunction([X|Xs], and(X, Conjunction)) 
    :-list_to_conjunction(Xs, Conjunction).

list_to_disjunction([X], X).
list_to_disjunction([X|Xs], or(X, Disjunction)) 
    :-list_to_disjunction(Xs, Disjunction).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% TODO: Eliminate ANDs

%% to_cnf(+Formula, -CNF).
to_cnf(_Formula, _CNF) :-
    true.

%% solve(+CNF).
solve(_CNF) :-
    true.
