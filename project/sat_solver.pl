:- module(sat_solver,[normalise/2, to_cnf/2, solve/1]).

:- load_test_files([]).

%% normalise(+Formula, -NFormula).
normalise(lit(X), X) 
    :-!.

normalise(not(implies(X, Y)), and(NX, NY)) 
    :-  normalise(X, NX), normalise(not(Y), NY).

normalise(not(equivalence(X, Y)), and(NX, NY)) 
    :-  normalise(not(implies(X,Y), NX)),
       normalise(not(implies(Y,X), NY)).

normalise(not(and(X,Y)), Norm)
    :- normalise(or(not(X),not(Y)), Norm).

normalise(not(or(X,Y)), Norm)
    :- normalise(and(not(X),not(Y)), Norm).

normalise(not(not(X)), NormalisedX) 
    :- normalise(X, NormalisedX).    

normalise(not(X), not(NX)) 
    :- normalise(X,NX).

normalise(and(X,Y), and(NX,NY)) 
    :- normalise(X,NX), normalise(Y,NY).

normalise(or(X, Y), or(NX, NY)) 
    :-  normalise(X, NX), normalise(Y, NY).

normalise(implies(X, Y), or(NX, NY)) 
    :-  normalise(not(X), NX), normalise(Y, NY).

normalise(equivalence(X, Y), and(NX, NY)) 
    :-  normalise(implies(X,Y), NX),
       normalise(implies(Y,X), NY).

normalise(min_one_pos(Vars), NormalisedForm)
    :- list_to_disjunction(Vars,Disjunction),
        normalise(Disjunction, NormalisedForm).

normalise(exactly_one_pos(Literals), NormalisedForm) :-
    findall(OrClause, pairwise_negation(Literals, OrClause), PairwiseNegations),
    list_to_disjunction(Literals, AtLeastOne),
    append(PairwiseNegations, [AtLeastOne], AllClauses),
    list_to_conjunction(AllClauses, Conjunctionss),
    normalise(Conjunctionss, NormalisedForm).

pairwise_negation(Literals, OrClause) :-
    select(Lit1, Literals, Remaining),
    member(Lit2, Remaining),
    Lit1 @< Lit2,
    OrClause = or(not(Lit1), not(Lit2)).

list_to_conjunction([X], X).
list_to_conjunction([X|Xs], and(X, Conjunction)) 
    :-list_to_conjunction(Xs, Conjunction).

list_to_disjunction([X], X).
list_to_disjunction([X|Xs], or(X, Disjunction)) 
    :-list_to_disjunction(Xs, Disjunction).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% to_cnf(+Formula, -CNF).
% Entry point for CNF conversion
to_cnf(Formula, CNF) :-
    normalise(Formula, NFormula),
    to_cnf_transformer(NFormula, CNF).

% Base case for literals and negated literals
to_cnf_transformer(X, X) :- is_literal(X), !.

to_cnf_transformer(not(X), not(NX)) 
    :- !, to_cnf_transformer(X,NX).

to_cnf_transformer(and(or(X,Y), or(Z,ZZ)), [[NX,NY],[NZ,NZZ]]) 
    :- !, to_cnf_transformer(X,NX), to_cnf_transformer(Y,NY), to_cnf_transformer(Z,NZ), to_cnf_transformer(ZZ,NZZ).


to_cnf_transformer(and(or(X,Y), Z), [[NX,NY],[NZ]]) 
    :- !, to_cnf_transformer(X,NX), to_cnf_transformer(Y,NY), to_cnf_transformer(Z,NZ).

to_cnf_transformer(and(Z,or(X,Y)), [[NZ], [NX,NY]]) 
    :- !, to_cnf_transformer(X,NX), to_cnf_transformer(Y,NY), to_cnf_transformer(Z,NZ).

to_cnf_transformer(and(X,Y), [[NX],[NY]]) 
    :- !, to_cnf_transformer(X,NX), to_cnf_transformer(Y,NY).

% Distributive laws for or
to_cnf_transformer(or(X, and(Y, Z)), NormalisedForm) :-
    !, to_cnf_transformer(or(X, Y), NX), to_cnf_transformer(or(X, Z), NZ), to_cnf_transformer(and(NX,NZ), NormalisedForm).

to_cnf_transformer(or(and(Y, Z), X), NormalisedForm) 
:- !, to_cnf_transformer(or(Y, X), NX), to_cnf_transformer(or(Z, X), NZ), to_cnf_transformer(and(NX,NZ), NormalisedForm).

to_cnf_transformer(or(X, Y), [NX,NY]) 
    :- !, to_cnf_transformer(X, NX), to_cnf_transformer(Y, NY).

is_literal(X) :- atom(X).
is_literal(not(X)) :- atom(X). 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%% solve(+CNF).
solve(_CNF) :-
    true.
