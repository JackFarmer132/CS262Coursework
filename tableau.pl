/* Dual Clause Form Program

Taken from Melvin Fitting, First-order logic and automated theorem proving, Springer.

Provided as template for creating resolution proof using similar constructs

Propositional operators are: neg, and, or, imp, revimp,
uparrow, downarrow, notimp, notrevimp */

?-op(140, fy, neg).
?-op(160, xfy, [and, or, imp, revimp, uparrow, downarrow, notimp, notrevimp]).

/* member(Item, List) :- Item occurs in list */

member(X, [X|_]).
member(X, [_|Tail]) :-
    member(X, Tail).

/* remove(Item, List, Newlist) :- removes Item from List and produces Newlist */

remove(X, [], []).
remove(X, [X|Tail], Newtail) :-
    remove(X, Tail, Newtail).
remove(X, [Head|Tail], [Head|Newtail]) :-
    remove(X, Tail, Newtail).

/* conjunctive(X) :- X is an alpha formula */

conjunctive(_ and _).
conjunctive(neg(_ or _)).
conjunctive(neg(_ imp _)).
conjunctive(neg(_ revimp _)).
conjunctive(neg(_ uparrow _)).
conjunctive(_ downarrow _).
conjunctive(_ notimp _).
conjunctive(_ notrevimp _).

/* disjunctive(X) :- X is beta formula */

disjunctive(neg(_ and _)).
disjunctive(_ or _).
disjunctive(_ imp _).
disjunctive(_ revimp _).
disjunctive(_ uparrow _).
disjunctive(neg(_ downarrow _)).
disjunctive(neg(_ notimp _)).
disjunctive(neg(_ notrevimp _)).

/* unary(X) :- X is a double negation or negated constant */

unary(neg neg _).
unary(neg true).
unary(neg false).

/* components(X,Y,Z) :- Y and Z are the components of formula X defined in a/b
                        table */

components(X and Y, X, Y).
components(neg(X and Y), neg X, neg Y).
components(X or Y, X, Y).
components(neg(X or Y), neg X, neg Y).
components(X imp Y, neg X, Y).
components(neg(X imp Y), X, neg Y).
components(X revimp Y, X, neg Y).
components(neg(X revimp Y), neg X, Y).
components(X uparrow Y, neg X, neg Y).
components(neg(X uparrow Y), X, Y).
components(X downarrow Y, neg X, neg Y).
components(neg(X downarrow Y), X, Y).
components(X notimp Y, X, neg Y).
components(neg(X notimp Y), neg X, Y).
components(X notrevimp Y, neg X, Y).
components(neg(X notrevimp Y), X, neg Y).

/* component(X,Y) :- Y is the componenet of the unary formula X */

component(neg neg X, X).
component(neg true, false).
component(neg false, true).

/* singlestep(Old,New) :- new is result of applying single step of expansion
                          process to Old, which is a generalised disjunction
                          of generalised conjunctions */

singlestep([Conjunction|Rest], New) :-
    member(Formula, Conjunction),
    unary(Formula),
    component(Formula, Newformula),
    remove(Formula, Conjunction, Temporary),
    Newconjunction = [Newformula, Temporary],
    New = [Newcon | Rest].

singlestep([Conjunction|Rest], New) :-
    member(Alpha, Conjunction),
    conjunctive(Alpha),
    components(Alpha, Alphaone, Alphatwo),
    remove(Alpha, Conjunction, Temporary),
    Newcon = [Alphaone, Alphatwo | Temporary],
    New = [Newcon | Rest].

singlestep([Conjunction|Rest], New) :-
    member(Beta, Conjunction),
    disjunctive(Beta),
    components(Beta, Betaone, Betatwo),
    remove(Beta, Conjunction, Temporary),
    Newconone = (Betaone | Temporary),
    Newcontwo = (Betatwo | Temporary),
    New = [Newconone, Newcontwo | Rest].

singlestep([Conjunction|Rest], [Conjunction, Newrest]) :-
    singlestep(Rest, Newrest).

/* expand(Old,New) :- New is result of applying singlestep as many times as
                      possible on Old */

expand(Dis, Newdis) :-
    singlestep(Dis, Temp),
    expand(Temp, Newdis).

expand(Dis, Dis).

/* dualclauseform(X,Y) :- Y is the dual clause form of X */

dualclauseform(X, Y) :-
    print("Thing is..."), print(X), nl,
    expand([[X]], Y).
