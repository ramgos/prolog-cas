:- use_module(library(clpfd)).
:- use_module('nunify.pl').

silent(G) :-
    catch(G, _, false).

% -----------------------------------------------------------------------%
% Simplification
% -----------------------------------------------------------------------%

reduced([X, /, Y], [W, /, Z]) :-
    Gcd is gcd(X, Y),
    W is X / Gcd,
    Z is Y / Gcd.

sum_(A, B, [A, +, B]).
sum_(A, B, [B, +, A]).
sum_(A, B, 0) :-
    sum_(A, B, [A0, +, B0]),
    product(A0, -1, B0).
product(A, B, [A, *, B]).
product(A, B, [B, *, A]).

% zero identities
simplify([0, /, _], 0).
simplify([0, ^, _], 0).
simplify([A, +, B], 0) :-
    sum_(A, B, 0).
simplify(A, 0) :-
    product(_, 0, A).

% same identites
simplify(A, As) :-
    sum_(As, 0, A).
simplify(A, As) :-
    product(As, 1, A).
simplify([A, ^, 1], A).

% double negation
simplify(A, As) :-
    product(-1, B, A),
    product(-1, As, B).

% one identities
simplify([1, ^, _], 1).
simplify([_, ^, 0], 1).
simplify([A, /, A], 1).

simplify([A, *, A], [A, ^, 2]).
simplify([A, +, A], B) :-
    product(A, 2, B).

% common factor rule
simplify(A, As) :-
    sum_(B, C, A),
    product(B, D, C),
    sum_(D, 1, E),
    product(B, E, As).
simplify(A, As) :-
    product(B, C, D),
    product(B, E, F),
    sum_(D, F, A),
    sum_(C, E, G),
    product(B, G, As).

% exponentiation rules same base
simplify(A, [B, ^, D]) :-
    product(B, [B, ^, C], A),
    sum_(C, 1, D).
simplify([[A, ^, B], *, [A, ^, C]], [A, ^, D]) :-
    sum_(B, C, D).
simplify([[A, ^, B], ^, C], [A, ^, D]) :-
    product(B, C, D).
simplify([[A, ^, B], /, A], [A, ^, C]) :-
    sum_(B, -1, C).
simplify([A, /, [A, ^, B]], [A, ^, C]) :-
    product(B, -1, Bm),
    sum_(Bm, 1, C).
simplify([[A, ^, B], /, [A, ^, C]], [A, ^, D]) :-
    product(C, -1, Cm),
    sum_(B, Cm, D).

% exponentiation rules same exponent
simplify([[B, ^, A], *, [C, ^, A]], [D, ^, A]) :-
    product(B, C, D).
simplify([[B, ^, A], /, [C, ^, A]], [[B, \, C], ^, A]).

% product of two divisions
simplify([[A, /, B], *, [C, /, D]], [Ac / Bd]) :-
    product(A, C, Ac),
    product(B, D, Bd).


simplify_exp_(X, X) :-
    nunify(X, [_, _, _]).
simplify_exp_([A, O, B], Simplified) :-
    nunify(A, [_, _, _]),
    nunify(B, [_, _, _]),
    simplify([A, O, B], Simplified).
simplify_exp_([A, O, B], Simplified) :-
    (   A = [_, _, _]
    ;   A \= [_, _, _],
        B = [_, _, _]
    ),
    simplify_exp_(A, As),
    simplify_exp_(B, Bs),
    (   simplify([As, O, Bs], Simplified)
    ;   dif([A, B], [As, Bs]),
        simplify_exp_([As, O, Bs], Simplified)
    ).
simplify_exp_([A, O, B], [A, O, B]) :-
    dif(A, As), dif(B, Bs),
    \+ simplify_exp_(A, As),
    \+ simplify_exp_(B, Bs).


simplify_exp(X, Y) :-
    dif(X, X1),
    partial_eval(X, X0),
    simplify_exp_(X0, X1),
    simplify_exp(X1, Y).
simplify_exp(X, X) :-
    dif(X, X1),
    partial_eval(X, X0),
    \+ simplify_exp_(X0, X1).


partial_eval(X, X) :-
    nunify(X, [_, _, _]).
partial_eval([A, O, B], V) :-
    nunify(A, [_, _, _]),
    nunify(B, [_, _, _]),
    silent(EvalExp =.. [O, A, B]),
    silent(V #= EvalExp).
partial_eval([A, /, B], [C, /, D]) :-
    silent(reduced([A, /, B], [C, /, D])).
partial_eval([A0, O, B0], [A, O, B]) :-
    \+
    (   silent(EvalExp =.. [O, A0, B0]),
        silent(_ #= EvalExp)
    ),
    partial_eval(A0, A),
    partial_eval(B0, B).

% -----------------------------------------------------------------------%
% Diffrentiation
% -----------------------------------------------------------------------%

not_expression_of(X, Y) :-
    dif(X, Y),
    nunify(Y, [_ | _]).
not_expression_of(X, Y) :-
    dif(X, Y),
    silent(Y = [A, _, B]),
    not_expression_of(X, A),
    not_expression_of(X, B).
not_expression_of(X, Y) :-
    dif(X, Y),
    silent(Y = [_, A]),
    not_expression_of(X, A).


derv(X, X, 1).
derv(X, Y, 0) :-
    dif(X, Y),
    nunify(Y, [_ | _]).
derv(X, Y, 0) :-
    dif(X, Y),
    Y = [_, _, _],
    not_expression_of(X, Y).

derv(X, [A, +, B], [AD, +, BD]) :-
    derv(X, A, AD),
    derv(X, B, BD).
derv(X, [A, *, B], [[AD, *, B], +, [A, *, BD]]) :-
    derv(X, A, AD),
    derv(X, B, BD).
derv(X, [A, ^, B], [[B, *, [A, ^, [B, +, -1]]], *, AD]) :-
    not_expression_of(X, B),
    derv(X, A, AD).
derv(X, [A, /, B], [[[AD, *, B], +,[-1, *, [A, *, BD]]], /, [B, ^, 2]]) :-
    derv(X, A, AD),
    derv(X, B, BD).



