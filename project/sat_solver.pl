:- module(sat_solver,[normalise/2, to_cnf/2, solve/1]).
:- load_test_files([]).

%% normalise(+Formula, -NFormula).

normalise(Formula,NFormula):-
    normalisation(Formula,Temp),
    (Formula \= Temp -> normalisation(Temp, NFormula); NFormula = Temp).

normalisation(lit(X), lit(X)) :- !.

normalisation(not(implies(X, Y)), and(NX, not(NY))) 
    :- !, normalisation(X, NX), normalise(Y, NY).

normalisation(not(and(not(X), not(Y))), or(NX, NY)) 
    :- !, normalisation(X, NX), normalise(Y, NY).

normalisation(not(and(X,Y)), Norm)
    :- !, normalisation(or(not(X),not(Y)), Norm).

normalisation(not(or(X,Y)), Norm)
    :- !, normalisation(and(not(X),not(Y)), Norm).

normalisation(not(not(X)), NormalisedX) :-
    !, normalisation(X, NormalisedX).

normalisation(not(X), not(NX)) 
    :- !, normalisation(X,NX).

normalisation(and(X,Y), and(NX,NY)) 
    :-!, normalisation(X,NX), normalisation(Y,NY).

normalisation(or(X, Y), or(NX, NY)) 
    :- !, normalisation(X, NX), normalisation(Y, NY).

normalisation(implies(X, Y), or(NX, NY)) 
    :- !,normalisation(not(X), NX), normalisation(Y, NY).

normalisation(equivalence(X, Y), NormalisedForm) :- !,
    normalisation(or(not(X), Y), LeftPart),
    normalisation(or(X, not(Y)), RightPart),
    NormalisedForm = and(LeftPart, RightPart).

normalisation(min_one_pos(Vars), NormalisedForm)
    :- !, list_to_disjunction(Vars,Disjunction),
        normalisation(Disjunction, NormalisedForm).

normalisation(exactly_one_pos(Literals), NormalisedForm) :- !,
    pairwise_negation(Literals, PairwiseNegations),
    list_to_disjunction(Literals, AtLeastOne),
    append(PairwiseNegations, [AtLeastOne], AllClauses),
    list_to_conjunction(AllClauses, Conjunctions),
    normalisation(Conjunctions, NormalisedForm).

pairwise_negation([], []) :- !.
pairwise_negation([Lit|Lits], PairwiseNegations) :- !,
    pairwise_negate(Lit, Lits, NegationsForLit),
    pairwise_negation(Lits, RemainingNegations),
    append(NegationsForLit, RemainingNegations, PairwiseNegations).

pairwise_negate(_, [], []) :- !.
pairwise_negate(Lit1, [Lit2|Lits], [OrClause|Rest]) :- !,
    Lit1 @< Lit2,
    OrClause = or(not(Lit1), not(Lit2)),
    pairwise_negate(Lit1, Lits, Rest).
pairwise_negate(Lit1, [_|Lits], Rest) :- !,
    pairwise_negate(Lit1, Lits, Rest).

list_to_conjunction([X], X) :- !.
list_to_conjunction([X|Xs], and(X, Conjunction)) 
    :- !, list_to_conjunction(Xs, Conjunction).

list_to_disjunction([X], X) :- !.
list_to_disjunction([X|Xs], or(X, Disjunction)) 
    :- !, list_to_disjunction(Xs, Disjunction).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

cleanup(lit(X), X) :- !.

cleanup(and(X, Y), and(CleanX, CleanY)) :- 
    !, cleanup(X, CleanX), cleanup(Y, CleanY).

cleanup(or(X, Y), or(CleanX, CleanY)) :- 
    !, cleanup(X, CleanX), cleanup(Y, CleanY).

cleanup(not(X), not(CleanX)) :- 
    !, cleanup(X, CleanX).
cleanup(X, X).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% to_cnf(+Formula, -CNF).
to_cnf(Formula, CNF) :-
    normalise(Formula, NFormula),
    cleanup(NFormula, CleanFormula),
    to_cnf_transformer(CleanFormula, CNFFormula),
    cnf_transform(CNFFormula, CNF), !.


to_cnf_transformer(X, CNF) :-
    is_literal(X), !, CNF = X. % Base case for literals

to_cnf_transformer(and(X, Y), and(CNF_X, CNF_Y)) :-
    !,
    to_cnf_transformer(X, CNF_X),
    to_cnf_transformer(Y, CNF_Y).

to_cnf_transformer(or(X, Y), CNF) :-
    !,
    ( is_literal(X), is_literal(Y) -> CNF = or(X, Y)
    ; is_literal(X) -> distribute_or(X, Y, CNF) 
    ; is_literal(Y) -> distribute_or(Y, X, CNF)
    ; to_cnf_transformer(X, CNF_X), to_cnf_transformer(Y, CNF_Y), distribute_or(CNF_X, CNF_Y, CNF)
    ).

distribute_or(X, Y, or(X, Y)).
distribute_or(X, and(Y, Z), and(CNF1, CNF2)) :-
    to_cnf_transformer(or(X, Y), CNF1),
    to_cnf_transformer(or(X, Z), CNF2).


% List of Lists Approach
cnf_transform(X, [[X]]) :- is_literal(X), !.
cnf_transform(not(X), [[not(X)]]) :- !,is_literal(X), !.

cnf_transform(and(X, Y), CNF) :-
    cnf_transform(X, CNFX),
    cnf_transform(Y, CNFY),
    append(CNFX, CNFY, CNF).

cnf_transform(or(X, Y), CNF) :-
    cnf_transform(X, CNFX),
    cnf_transform(Y, CNFY),
    distribute_or_(CNFX, CNFY, CNF).

distribute_or_([], _, []).
distribute_or_([H|T], CNFY, CNF) :-
    distribute_or_clause(H, CNFY, CNF1),
    distribute_or_(T, CNFY, CNF2),
    append(CNF1, CNF2, CNF).

distribute_or_clause(_, [], []).
distribute_or_clause(ClauseX, [ClauseY|T], [CNF|CNFs]) :-
    append(ClauseX, ClauseY, CNF),
    distribute_or_clause(ClauseX, T, CNFs).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

is_literal(X) :- var(X), !.  
is_literal(not(X)) :- var(X), !.  

is_literal(true) :- !.
is_literal(false) :- !.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% solve(+CNF)
solve(CNF) :-
    davis_putnam_logemann_loveland(CNF).

davis_putnam_logemann_loveland([]).
davis_putnam_logemann_loveland(CNF) :- 
    select([Unit], CNF, NewCNF), !,
    assign_value_to_Unit(Unit),
    propagate_simplify(NewCNF,SimplifiedCNF),
    davis_putnam_logemann_loveland(SimplifiedCNF).
davis_putnam_logemann_loveland(CNF) :-
    \+ (member(Unit,CNF), is_unit_clause(Unit)),
    assign_value_to_random(CNF),
    propagate_simplify(CNF, SimplifiedCNF),
    davis_putnam_logemann_loveland(SimplifiedCNF).

assign_value_to_Unit(X) :-
    ( var(X) -> X = true ; X = not(Y), var(Y) -> Y = false).

is_unit_clause([X]) :- var(X); X == true; X == false.               
is_unit_clause([not(X)]) :- var(X). 

assign_value_to_random(CNF) :- 
    select_unassigned_variable(CNF, Var),
    (Var = true ; Var = false). % choice point

select_unassigned_variable(CNF, Var) :-
    member(Clause, CNF),
    member(Literal, Clause),
    var(Literal),
    Var = Literal,
    !.
    
propagate_simplify([], []). 
propagate_simplify([Clause|Rest], Result) :-
    (   member_(Clause, true)
    ->  propagate_simplify(Rest, Result) 
        ;   
        member_(Clause, not(false))
    -> propagate_simplify(Rest, Result)
        ;
        member_(Clause, false)
        -> 
     del(false, Clause, NewClause), 
        Result = [NewClause|NewRest], 
        propagate_simplify(Rest, NewRest)
    ;
        member_(Clause, not(true))
        -> 
     del(not(true), Clause, NewClause), 
        Result = [NewClause|NewRest], 
        propagate_simplify(Rest, NewRest)
    ;   Result = [Clause|NewRest], 
        propagate_simplify(Rest, NewRest)
    ).

% write own helper because of unification of member

del(_,[],[]) :-!.
del(X,[H|T],LIST1):- X == H, del(X,T,LIST1).
del(X,[H|T],[H|LIST1]) :- X \== H, del(X,T,LIST1).

member_([H|_], Term) :-
    (nonvar(H), H == Term -> H = Term).
member_([_|T], Term) :-
    member_(T, Term).
