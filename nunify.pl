:- module(nunify, [nunify / 2]).

nunify(X, Y) :-
    var(X),
    \+ get_attr(X, nunify, _),
    put_attr(X, nunify, [Y]).
nunify(X, Y) :-
    var(X),
    get_attr(X, nunify, NunifyOld),
    append(NunifyOld, [Y], NunifyNew),
    put_attr(X, nunify, NunifyNew).
nunify(X, Y) :-
    nonvar(X),
    X \= Y.

attr_unify_hook(Nunify, X) :-
    maplist(nunify(X), Nunify).

nunify_chain(X, [Nunify0]) -->
    [nunify(X, Nunify0)].
nunify_chain(X, [Nunify0 | NunifyRest]) -->
    [nunify(X, Nunify0)],
    nunify_chain(X, NunifyRest).

attribute_goals(X) -->
    { get_attr(X, nunify, Nunify) },
    nunify_chain(X, Nunify).
