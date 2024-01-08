:- module(sat_solver,[normalise/2, to_cnf/2, solve/1]).
:- load_test_files([]).

%% normalise(+Formula, -NFormula).
normalise(lit(X), X) :-
    is_literal(X), !.

normalise(not(implies(X, Y)), and(NX, NY)) 
    :- !,  normalise(X, NX), normalise(not(Y), NY).

normalise(not(and(X,Y)), Norm)
    :- !, normalise(or(not(X),not(Y)), Norm).

normalise(not(or(X,Y)), Norm)
    :- !, normalise(and(not(X),not(Y)), Norm).

normalise(not(not(X)), NormalisedX) :-
    !, normalise(X, NormalisedX).

normalise(not(X), not(NX)) 
    :- !, normalise(X,NX).

normalise(and(X,Y), and(NX,NY)) 
    :-!, normalise(X,NX), normalise(Y,NY).

normalise(or(X, Y), or(NX, NY)) 
    :- !, normalise(X, NX), normalise(Y, NY).

normalise(implies(X, Y), or(NX, NY)) 
    :- !,normalise(not(X), NX), normalise(Y, NY).

normalise(equivalence(X, Y), NormalisedForm) :- !,
    normalise(or(not(X), Y), LeftPart),
    normalise(or(X, not(Y)), RightPart),
    NormalisedForm = and(LeftPart, RightPart).

normalise(min_one_pos(Vars), NormalisedForm)
    :- !, list_to_disjunction(Vars,Disjunction),
        normalise(Disjunction, NormalisedForm).

normalise(exactly_one_pos(Literals), NormalisedForm) :- !,
    pairwise_negation(Literals, PairwiseNegations),
    list_to_disjunction(Literals, AtLeastOne),
    append(PairwiseNegations, [AtLeastOne], AllClauses),
    list_to_conjunction(AllClauses, Conjunctions),
    normalise(Conjunctions, NormalisedForm).

pairwise_negation([], []).
pairwise_negation([Lit|Lits], PairwiseNegations) :-
    pairwise_negate(Lit, Lits, NegationsForLit),
    pairwise_negation(Lits, RemainingNegations),
    append(NegationsForLit, RemainingNegations, PairwiseNegations).

pairwise_negate(_, [], []).
pairwise_negate(Lit1, [Lit2|Lits], [OrClause|Rest]) :-
    Lit1 @< Lit2,
    OrClause = or(not(Lit1), not(Lit2)),
    pairwise_negate(Lit1, Lits, Rest).
pairwise_negate(Lit1, [_|Lits], Rest) :-
    pairwise_negate(Lit1, Lits, Rest).

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
    ( Transformed == PrevFormula -> CNF = Transformed;  % Base case: no further transformation
      is_cnf(Transformed) -> CNF = Transformed;         % Base case: already in CNF
      % Recursive case: Transform until no changes
      to_cnf_with_check(Transformed, Transformed, CNF)
    ).
                         

is_cnf(and(_,_)) :- !.
is_cnf(X) :- is_literal(X).
is_cnf(not(X)) :- is_literal(X).

is_dnf(or(_,_)) :- !.
is_dnf(X) :- is_literal(X).
is_dnf(not(X)) :- is_literal(X).


to_cnf_transformer(X, CNF) :-
    is_literal(X), !, CNF = X. % Base case for literals

to_cnf_transformer(and(X, Y), and(CNF_X, CNF_Y)) :-
    to_cnf_transformer(X, CNF_X),
    to_cnf_transformer(Y, CNF_Y).

to_cnf_transformer(or(X, Y), CNF) :-
    ( is_literal(X), is_literal(Y) -> CNF = or(X, Y) % Base case for disjunction of literals
    ; is_literal(X) -> distribute_or(X, Y, CNF) % Distribute X over Y
    ; is_literal(Y) -> distribute_or(Y, X, CNF) % Distribute Y over X
    ; to_cnf_transformer(X, CNF_X), to_cnf_transformer(Y, CNF_Y), distribute_or(CNF_X, CNF_Y, CNF)
    ).

% Helper predicate to distribute disjunction over conjunction
distribute_or(X, and(Y, Z), and(CNF1, CNF2)) :-
    to_cnf_transformer(or(X, Y), CNF1),
    to_cnf_transformer(or(X, Z), CNF2).

distribute_or(X, Y, or(X, Y)). % Base case for distribution


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
solve(CNF) :-
    unit_propagation(CNF, PropagatedCNF),
    check_cnf_status(PropagatedCNF, Status),
    (   Status = unsat -> fail       % If UNSAT after unit propagation, fail immediately.
    ;   Status = sat -> true         % If CNF is empty after unit propagation, succeed.
    ;   branch(PropagatedCNF)        % Otherwise, perform variable branching.
    ).

% Branching on a variable
branch(CNF) :-
    select_var(CNF, Var),            % Select an unassigned variable
    (   propagate_and_solve(Var, CNF)  % Propagate true, then solve
    ;   propagate_and_solve(not(Var), CNF)  % Propagate false, then solve
    ).

propagate_and_solve(Var, CNF) :-
    propagate_unit(Var, CNF, ModifiedCNF),  % Apply the variable assignment
    solve(ModifiedCNF).                     % Recursively solve the modified CNF

% Select a variable to branch on
select_var(CNF, Var) :-
    findall(V, (member(Clause, CNF), member(Lit, Clause), var_lit(Lit, V)), Vars),
    list_to_set(Vars, VarSet),
    member(Var, VarSet).

% Extract variable from a literal (either positive or negated)
var_lit(X, X) :- var(X); X == true; X == false, !.
var_lit(not(X), X) :- var(X).

unit_propagation(CNF, CNF) :- % Base case: stop when no unit clause is found
    \+ (member(Unit, CNF), is_unit_clause(Unit)),
    !.

unit_propagation(CNF, NNCNF) :- 
    member(Unit, CNF),
    is_unit_clause(Unit),
    propagate_unit(Unit, CNF, NCNF),
    unit_propagation(NCNF, NNCNF).

contains_var(Var, [H|_]) :- 
    get_single_element(Var,SVar),     
    H == SVar,   
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

is_unit_clause([X]) :- var(X); X == true; X == false, !.                  % Single variable
is_unit_clause([not(X)]) :- var(X), !.             % Single negated variable

check_cnf_status([], sat).
check_cnf_status(CNF, Status) :-
    % Check if there is an empty clause in the CNF.
    (   member([], CNF)
    ->  Status = unsat
    ;   Status = undefined
    ).