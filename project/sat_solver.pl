:- module(sat_solver,[normalise/2, to_cnf/2, solve/2]).
:- load_test_files([]).

%% normalise(+Formula, -NFormula).
normalise(lit(X), X) :-
    is_literal(X).

normalise(not(implies(X, Y)), and(NX, NY)) 
    :-  normalise(X, NX), normalise(not(Y), NY).

normalise(not(and(X,Y)), Norm)
    :- normalise(or(not(X),not(Y)), Norm).

normalise(not(or(X,Y)), Norm)
    :- normalise(and(not(X),not(Y)), Norm).

normalise(not(not(X)), NormalisedX) :-
    !, normalise(X, NormalisedX).

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
to_cnf(Formula, CNF) :-
    normalise(Formula, NFormula),
    to_cnf_with_check(NFormula, NFormula, CNFFormula),
    cnf_transform(CNFFormula, CNF).

to_cnf_with_check(Formula, PrevFormula, CNF) :-
    to_cnf_transformer(Formula, Transformed),
    (Transformed == PrevFormula -> CNF = Transformed;  
     is_cnf(Transformed) -> CNF = Transformed;       
     is_dnf(Transformed) -> to_cnf_with_check(Transformed, Formula, CNF);  
     CNF = Transformed).                            

is_cnf(and(_,_)) :- !.
is_cnf(X) :- is_literal(X).
is_cnf(not(X)) :- is_literal(X).

is_dnf(or(_,_)) :- !.
is_dnf(X) :- is_literal(X).
is_dnf(not(X)) :- is_literal(X).

to_cnf_transformer(X, X) :- is_literal(X), !.

to_cnf_transformer(or(X, Y), or(X, Y)) :- is_literal(X), is_literal(Y), !.

to_cnf_transformer(and(X, Y), and(NX, NY)) :-
    !, to_cnf_transformer(X, NX), to_cnf_transformer(Y, NY).

to_cnf_transformer(or(X, and(Y, Z)), NormalisedForm) :-
    !, to_cnf_transformer(or(X, Y), NX), to_cnf_transformer(or(X, Z), NZ),
    to_cnf_transformer(and(NX, NZ), NormalisedForm).
to_cnf_transformer(or(and(Y, Z), X), NormalisedForm) :-
    !, to_cnf_transformer(or(Y, X), NY), to_cnf_transformer(or(Z, X), NZ),
    to_cnf_transformer(and(NY, NZ), NormalisedForm).

to_cnf_transformer(or(X, Y), or(NX, NY)) :-
    !, to_cnf_transformer(X, NX), to_cnf_transformer(Y, NY).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

cnf_transform(X, [[X]]) :- 
    is_literal(X),!.

cnf_transform(not(X), [[not(X)]]) :-
    is_literal(X),!.

cnf_transform(and(X, Y), CNF) :-
    !, cnf_transform(X, CNFX),
    cnf_transform(Y, CNFY),
    append(CNFX, CNFY, CNF).

cnf_transform(or(X, Y), [Clause]) :-
    !, cnf_clause(X, ClauseX),
    cnf_clause(Y, ClauseY),
    append(ClauseX, ClauseY, Clause).

cnf_clause(X, [X]) :- is_literal(X), !.

cnf_clause(or(X, Y), Clause) :-
    !, cnf_clause(X, ClauseX),
    cnf_clause(Y, ClauseY),
    append(ClauseX, ClauseY, Clause).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

is_literal(X) :- var(X), !.  
is_literal(not(X)) :- var(X), !.  

is_literal(true) :- !.
is_literal(false) :- !.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% solve(+CNF)
solve(CNF, OUT) :-
    unit_propagation(CNF, OUT).

unit_propagation(CNF, CNF) :- % Base case: stop when no unit clause is found
    \+ (member(Unit, CNF), is_unit_clause(Unit)),
    !.

unit_propagation(CNF, NNCNF) :- 
    member(Unit, CNF),
    is_unit_clause(Unit),
    propagate_unit(Unit, CNF, NCNF),
    unit_propagation(NCNF, NNCNF).

contains_var(Var, [H|_]) :-      
    [H] == Var,   
    !.
contains_var(Var, [_|T]) :-
    contains_var(T, Var).

get_single_element([Element], Element).

contains_neg_var(Var, [H|_]) :-
    get_single_element(Var,SVar),
    match(H,not(SVar)), !.           
contains_neg_var(Var, [_|T]) :-
    contains_neg_var(Var, T).

propagate_unit(Var, CNF, NCNF) :-
    process_clauses(Var, CNF, NCNF).


process_clauses(_, [], []). 
process_clauses(Var, [Clause|Rest], Result) :-
    (   contains_var(Var, Clause)
    ->  process_clauses(Var, Rest, Result)  % Skip the clause if it contains Var
    ;   
    contains_neg_var(Var, Clause)
        -> get_single_element(Var, SVar),
     del(not(SVar), Clause, NewClause), 
        Result = [NewClause|NewRest], 
        process_clauses(Var, Rest, NewRest)
    ;   Result = [Clause|NewRest], 
        process_clauses(Var, Rest, NewRest)
    ).

del(Y,[Y],[]).
del(X,[X|LIST1],LIST1).
del(X,[Y|LIST], [Y|LIST1]) :-del(X,LIST,LIST1).

match(H,SVar) :- 
    H == SVar;
    not(not(H)) == SVar.

is_unit_clause([X]) :- var(X), !.                  % Single variable
is_unit_clause([not(X)]) :- var(X), !.             % Single negated variable