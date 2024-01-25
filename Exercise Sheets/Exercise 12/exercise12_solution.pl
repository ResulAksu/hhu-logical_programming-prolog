:- use_module(library(plunit)).

% Task 2

%a
toDL(L, X, R) :- append(L, R, X).

%b
dlconcat(DL1-DLT1, DLT1-DLT2, DL1-DLT2).

%c
%member(X, []) :- fail.
%member(X, [X|_]).
%member(X, [H|T]) :-
%    X \= H,
%    member(X,T).

%dlmember(3, [1,2,3]-[3]).
%dlmember(2, [1,2,3]-[3]).
%dlmember(3, [1,2,3]-[1,2,3]).

dlmember(_, DL-R) :-
    DL == R, !,
    fail.

dlmember(X, [X|_]-_).
dlmember(X, [H|T]-D) :-
    X \== H,
    dlmember(X, T-D).

% Task 3

parse_pars(Term, N) :-
    string_codes(Term, TermList),
    % bracket(N, TermList, []). % instead of phrase
    phrase(bracket(N), TermList).

% with atom_chars
%bracket(0) --> [].
%bracket(N) --> ['('], bracket(TmpN), [')'], {N is TmpN + 1}.
%bracket(N) --> ['<'], bracket(TmpN), ['>'], {N is TmpN + 1}.
%bracket(N) --> ['['], bracket(TmpN), [']'], {N is TmpN + 1}.
%bracket(N) --> ['{'], bracket(TmpN), ['}'], {N is TmpN + 1}.

bracket(0) --> "".
bracket(N) --> "(", bracket(TmpN), ")", {N is TmpN + 1}.
bracket(N) --> "<", bracket(TmpN), ">", {N is TmpN + 1}.
bracket(N) --> "[", bracket(TmpN), "]", {N is TmpN + 1}.
bracket(N) --> "{", bracket(TmpN), "}", {N is TmpN + 1}.

% Task 4

remove_empty_list([], []).
remove_empty_list([[]|T], R) :- remove_empty_list(T, R).
remove_empty_list([H|T], [H|R]) :-
    H \= [],
    remove_empty_list(T, R).

parse_sudoku(FilePath, Sudoku) :-
    phrase_from_file(sudoku_input(TmpSudoku), FilePath),
    remove_empty_list(TmpSudoku, Sudoku).


sudoku_input([Row|T]) --> sudoku_row(Row), sudoku_input(T).
sudoku_input([]) --> "".

sudoku_row([]) --> "\n".
sudoku_row(T) --> ("|"; "+"; "-"; " "), !, sudoku_row(T).
sudoku_row([_|T]) -->  "X", !, sudoku_row(T).

sudoku_row([Num|T]) -->  [D1, D2], {on_exception(_, number_codes(Num, [D1, D2]), fail)}, sudoku_row(T).
sudoku_row([Num|T]) -->  [D], {on_exception(_, number_codes(Num, [D]), fail)}, sudoku_row(T).




:- begin_tests(to_dl).

test(to_dl1, [nondet,true(X = [a,b,c|R])]) :-
    toDL([a,b,c], X, R).

test(to_dl2, [nondet]) :-
    toDL([a,b], [a,b,c],[c]).

test(to_dl3, [true(X = [a,b,c,d])]) :-
    toDL([a,b], X, [c,d]).

:- end_tests(to_dl).

:- begin_tests(dlconcat).

test(dlconcat1, [nondet,true([List,A] = [[a,b,c,d,e,f|B]-B,[d,e,f|B]])]) :-
    dlconcat([a,b,c|A]-A, [d,e,f|B]-B, List).

test(dlconcat2, [nondet,true([List,A] = [[a,b,c|B]-B,B])]) :-
    dlconcat([a,b,c|A]-A, B-B, List).

test(dlconcat3, [nondet,true([List,A] = [B-B,B])]) :-
    dlconcat(A-A, B-B, List).

test(dlconcat4, [nondet,true([List,A] = [[a,b,c,f(a),"1","2","3"|B]-B,["1","2","3"|B]])]) :-
    dlconcat([a,b,c,f(a)|A]-A, ["1","2","3"|B]-B, List).

:- end_tests(dlconcat).

:- begin_tests(dlmember).

test(dlmember1, [all(A == [a,b,c])]) :-
    dlmember(A, [a,b,c|R]-R).

test(dlmember2, [all(A == [[a,b,c],1,3])]) :-
    dlmember(A, [[a,b,c],1,3|R]-R).

test(dlmember_fail1, [fail]) :-
    dlmember(1, [a,b,c|R]-R).

test(dlmember_fail2, [fail]) :-
    dlmember(a, R-R).

:- end_tests(dlmember).


:- begin_tests(parser).

test(parse1, [all(N == [1])]) :-
    parse_pars(`()`, N).

test(parse2, [all(N == [4])]) :-
    parse_pars(`{([<>])}`, N).

test(parse3, [nondet,all(N == [1])]) :-
    parse_pars("()", N).

test(parse4, [nondet,all(N == [4])]) :-
    parse_pars("{([<>])}", N).

test(parse5, [nondet,all(N == [0])]) :-
    parse_pars(``, N).

test(parse6, [nondet,all(N == [23])]) :-
    parse_pars(`([{((((((((<[{[<{([{<<<>>>}])}>]}]>))))))))}])`, N).

test(parse7, [nondet,all(N == [3])]) :-
    parse_pars("((()))", N).

test(parse_fail1, [fail]) :-
    parse_pars(`{([<>)}`,_) , !.

test(parse_fail2, [fail]) :-
    parse_pars(`([{<>}<]>)`,_) , !.

test(parse_fail3, [fail]) :-
    parse_pars(`([{<([{]})>}])`,_) , !.

:- end_tests(parser).


:- begin_tests(sudoku_parser).

test(parse_sudoku1, [all(Sudoku = [[[_,_,_,_],[_,_,_,_],[_,_,_,_],[_,_,_,_]]])]) :-
    parse_sudoku('./sudoku_puzzles/sud4x4.txt', Sudoku).

test(parse_sudoku2, [all(Sudoku = [[[_,3,_,_,_,_,_,_,_],[_,_,_,1,9,5,_,_,_],[_,_,8,_,_,_,_,6,_],[8,_,_,_,6,_,_,_,_],[4,_,_,8,_,_,_,_,1],[_,_,_,_,2,_,_,_,_],[_,6,_,_,_,_,2,8,_],[_,_,_,4,1,9,_,_,5],[_,_,_,_,_,_,_,7,_]]])]) :-
    parse_sudoku('./sudoku_puzzles/sud9x9.txt', Sudoku).

:- end_tests(sudoku_parser).

print_sudoku(Sudoku) :-
    nl,
    print_sudoku_rows(Sudoku).

print_sudoku_rows([]) :- nl.
print_sudoku_rows([Row|T]) :-
    print_sudoku_row(Row),
    print_sudoku_rows(T).

print_sudoku_row([]) :- nl.
print_sudoku_row([Nr|T]) :-
    format("~w ", [Nr]),
    print_sudoku_row(T).