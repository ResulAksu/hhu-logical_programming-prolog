:- module(sat_solver,[normalise/2, to_cnf/2, solve/1]).

:- load_test_files([]).

%% normalise(+Formula, -NFormula).
normalise(X, X) :- atom(X).

normalise(lit(X), X) 
    :-!.

normalise(not(implies(X, Y)), and(NX, NY)) 
    :-  normalise(X, NX), normalise(not(Y), NY).

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
    :- normalise(not(X), NX), normalise(Y, NY).

normalise(equivalence(X, Y), NormalisedForm) :-
    normalise(not(X), NX),
    normalise(not(Y), NY),
    normalise(or(NX, Y), LeftPart),
    normalise(or(X, NY), RightPart),
    NormalisedForm = and(LeftPart, RightPart).

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
% Entry point for CNF conversion with checker
to_cnf(Formula, CNF) :-
    normalise(Formula, NFormula),
    to_cnf_with_check(NFormula, NFormula, CNF).

% Apply CNF transformation with checks for CNF, DNF, and changes
to_cnf_with_check(Formula, PrevFormula, CNF) :-
    to_cnf_transformer(Formula, Transformed),
    (Transformed == PrevFormula -> CNF = Transformed;  % No change, formula is in CNF or cannot be transformed further
     is_cnf(Transformed) -> CNF = Transformed;        % Formula is in CNF
     is_dnf(Transformed) -> to_cnf_with_check(Transformed, Formula, CNF);  % Formula is in DNF, keep transforming
     CNF = Transformed).                             % Formula is neither CNF nor DNF, but cannot be transformed further


% Check if a formula is in CNF
is_cnf(and(_,_)) :- !.
is_cnf(X) :- is_literal(X).
is_cnf(not(X)) :- is_literal(X).

% Check if a formula is in DNF
is_dnf(or(_,_)) :- !.
is_dnf(X) :- is_literal(X).
is_dnf(not(X)) :- is_literal(X).
% Base cases for literals and negated literals
to_cnf_transformer(X, X) :- is_literal(X), !.
to_cnf_transformer(not(X), not(NX)) :- is_literal(X), !, NX = X.

% Apply distributive laws
to_cnf_transformer(or(X, and(Y, Z)), NormalisedForm) :-
    !, to_cnf_transformer(or(X, Y), NX), to_cnf_transformer(or(X, Z), NZ), to_cnf_transformer(and(NX, NZ), NormalisedForm).

to_cnf_transformer(or(and(Y, Z), X), NormalisedForm) :-
    !, to_cnf_transformer(or(Y, X), NY), to_cnf_transformer(or(Z, X), NZ), to_cnf_transformer(and(NY, NZ), NormalisedForm).

% Recursively apply transformations for other and/or combinations
to_cnf_transformer(and(X, Y), and(NX, NY)) :-
    !, to_cnf_transformer(X, NX), to_cnf_transformer(Y, NY).

to_cnf_transformer(or(X, Y), or(NX, NY)) :-
    !, to_cnf_transformer(X, NX), to_cnf_transformer(Y, NY).

is_literal(X) :- atom(X).
is_literal(not(X)) :- atom(X).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%% solve(+CNF).
solve(_CNF) :-
    true.
