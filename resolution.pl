/*
1. YES
2. YES
3. YES
4. NO
5. YES
6.
7. YES
8. NO
9. NO
10. YES
*/


/* initialise opeartors and their precedence */
?-op(140, fy, neg).
?-op(160, xfy, [and, or, imp, revimp, uparrow, downarrow, notimp, notrevimp, equiv, notequiv]).

/*
    ====================
    Auxillary Operations
    ====================
*/

/* member(Item,List) :- item occurs in list */
member(X, [X|_]).
member(X, [_|Tail]) :-
    member(X, Tail).


/* memberprime(Formula,List) :- will see if a semantically equivilent formula
                                exists in the list */
memberprime(X, [Head|Tail]) :-
    equivformula(X, Head).
memberprime(X, [_|Tail]) :-
    member(X, Tail).


/* reduce(List,Temp,Newlist) :- will take in a list and return one where every
                                element occurs only once */
reduce([], Temp, Temp).
reduce([Head | Rest], Temp, Newlist) :-
    member(Head, Temp),
    reduce(Rest, Temp, Newlist).
reduce([Head | Rest], Temp, Newlist) :-
    not(member(Head, Temp)),
    reduce(Rest, [Head | Temp], Newlist).


/* reduceall(List,Newlist) :- will take in a list of lists, apply reduce() to
                              all and return the greater, simplified list */
reduceall([], Temp, Temp).
reduceall([Head | Rest], Temp, Newlist) :-
    reduce(Head, [], Newhead),
    reduceall(Rest, [Newhead | Temp], Newlist).



/* removesingle(Item,List,Newlist) :- will remove only 1 occurence of the Item
                                      from the list */
removesingle(Item, [], []) :- !.
removesingle(Item, [Item | Rest], Newlist) :-
    !, Newlist = Rest.
removesingle(Item, [Head | Rest], Newlistone) :-
    !, removesingle(Item, Rest, Newlisttwo),
    append([Head], Newlisttwo, Newlistone).


/* removeall(Item,List,Newlist) :- removes all occurences of the Item from
                                   the provided list*/
removeall(Item, [], []) :- !.
removeall(Item, [Item |Rest], Newlist) :-
    !, removeall(Item, Rest, Newlist).
removeall(Item, [Head | Rest], Newlistone) :-
    !, removeall(Item, Rest, Newlisttwo),
    append([Head], Newlisttwo, Newlistone).



/* append(List1,List2,List3) :- will combine lists 1 and 2 into a single list */
append([Head | Rest], List2, [Head | Newrest]) :-
    append(Rest, List2, Newrest).
append([], Newlist, Newlist).


/* fetch(Element,Biglist,Return) :- searches through a list of lists to see if
                                    the element exists in any of them. if it
                                    does, return the list with the element
                                    present */
fetch(Element, [List | Rest], Return) :-
    member(Element, List),
    Return = List.
fetch(Element, [_ | Rest], Return) :-
    fetch(Element, Rest, Return).


/* if_then_else(A,B,C) :- if A holds then perform B, otherwise perform C */
if_then_else(A, B, C) :-
    A,
    !, B.
if_then_else(A, B, C) :-
    C.


/* equivformula(Formulaone,Formulatwo) :- will compare each formula to see if
                                          they are sematically equivilent */
equivformula(neg Formulaone, neg Formulatwo) :-
    equivformula(Formulaone, Formulatwo).
equivformula(Atomone, Atomtwo) :-
    Atomone == Atomtwo.
equivformula(Formulaone, Formulatwo) :-
    strip(Formulaone, X1, Y1),
    strip(Formulatwo, X2, Y2),
    ((equivformula(X1, X2), equivformula(Y1, Y2));
     (equivformula(X1, Y2), equivformula(Y1, X2))).

/*
   ==================
   Logical Operations
   ==================
*/

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


/* equivilent(X) :- X involves an equivilence operation */
equivilent(_ equiv _).
equivilent(_ notequiv _).
equivilent(neg(_ equiv _)).
equivilent(neg(_ notequiv _)).


/* unary(X) :- X is a double negation or negated constant */
unary(neg neg _).
unary(neg true).
unary(neg false).


/* immediateequiv(X) :- signals when a new formula is of the specific form
                        'X equiv Y' */
immediateequiv(_ equiv _).


/* immediatenotequiv(X) :- signals when a new formula is of the specific form
                           'X notequiv Y' */
immediatenotequiv(_ notequiv _).


/* components(X,Y,Z) :- Y and Z are the components of formula X */
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


/* component(X,Y) :- Y is the component of the unary formula X */
component(neg neg X, X).
component(neg true, false).
component(neg false, true).


/* component(X,Y) :- Y is the semantically identical to X (where X involes
                     equivilence), just rewritten in terms of and, neg and
                     or */
component(X equiv Y, (neg X or Y) and (X or neg Y)).
component(neg(X equiv Y), (neg X or neg Y) and (X or Y)).
component(X notequiv Y, (neg X or neg Y) and (X or Y)).
component(neg(X notequiv Y), (neg X or Y) and (X or neg Y)).


/* strip(Formula, X, Y) :- breaks down Formula into atomic parts, only for
                           those where the order of the variables does not
                           matter */
strip(X equiv Y, X, Y).
strip(X notequiv Y, X, Y).
strip(X and Y, X, Y).
strip(X or Y, X, Y).
strip(X uparrow Y, X, Y).
strip(X downarrow Y, X, Y).

/*
   ================
   Proof Operations
   ================
*/

/* test(Formula) :- will print YES is formula is a tautology, NO otherwise */
test(Formula) :-
    immediateequiv(Formula),
    strip(Formula, X, Y),
    equivformula(X, Y),
    print("YES").
test(Formula) :-
    immediatenotequiv(Formula),
    strip(Formula, X, Y),
    equivformula(X, Y),
    print("NO").
test(Formula) :-
    if_then_else(prove([[neg Formula]]), print("YES"), print("NO")).


/* prove(Formula) :- applies CNF conversion on Formula, applying resolution
                     rules after each step in attempt to conclude proof early */
prove(Formula) :-
    reduceall(Formula, [], Temp),
    resolution(Temp).
prove(Formula) :-
    singlestep(Formula, Temp),
    !, prove(Temp).


/* singlestep(Old,New) :- new is result of applying single step of expansion
                          process to Old, which is a generalised conjunction
                          of generalised disjunctions */
/* dealing with unary operator */
singlestep([Disjunction|Rest], New) :-
    member(Formula, Disjunction),
    unary(Formula),
    component(Formula, Newformula),
    removeall(Formula, Disjunction, Temporary),
    append([Newformula], Temporary, Newdisjunction),
    New = [Newdisjunction | Rest].

/* dealing with equiv formula */
singlestep([Disjunction|Rest], New) :-
    member(Formula, Disjunction),
    equivilent(Formula),
    component(Formula, Newformula),
    removeall(Formula, Disjunction, Temporary),
    append([Newformula], Temporary, Newdisjunction),
    New = [Newdisjunction | Rest].

/* dealing with alpha formula */
singlestep([Disjunction|Rest], New) :-
    member(Alpha, Disjunction),
    conjunctive(Alpha),
    components(Alpha, Alphaone, Alphatwo),
    removeall(Alpha, Disjunction, Temporary),
    append([Alphaone], Temporary, Newdisone),
    append([Alphatwo], Temporary, Newdistwo),
    New = [Newdisone, Newdistwo | Rest].

/* dealing with beta formula */
singlestep([Disjunction|Rest], New) :-
    member(Beta, Disjunction),
    disjunctive(Beta),
    components(Beta, Betaone, Betatwo),
    removeall(Beta, Disjunction, Temporary),
    Newdis = [Betaone, Betatwo | Temporary],
    New = [Newdis | Rest].

singlestep([Disjunction|Rest], New) :-
    singlestep(Rest, Newrest),
    append([Disjunction], Newrest, New).


/* resolution(Formula) :- conducts all possible combinations of resolution
                          rules on the provided disjunctions within Formula,
                          succeeding if the empty list is ever encountered */
resolution(Res) :-
    member([], Res).
resolution(Res) :-
    resolutionstep(Res, Temp),
    resolution(Temp).


/* resolutionstep(Old,New) :- New is result of applying single step of
                              resolution process to Old */
/* trivial resolvant case */
resolutionstep([Disjunction|Rest], New) :-
    member(false, Disjunction),
    removeall(false, Disjunction, Temp),
    New = [Temp | Rest].

/* non-negated formulaic resolution rule */
resolutionstep([Dis1|Rest], New) :-
    memberprime(Formula, Dis1),
    (unary(Formula); equivilent(Formula); conjunctive(Formula); disjunctive(Formula)),
    fetch(neg Formula, Rest, Dis2),
    removeall(Formula, Dis1, Temp1),
    removeall(neg Formula, Dis2, Temp2),
    append(Temp1, Temp2, Newdis),
    removesingle(Dis2, Rest, Newrest),
    not(Rest = Newrest),
    append([Newdis], Newrest, New).

/* negated formulaic resolution rule */
resolutionstep([Dis1|Rest], New) :-
    memberprime(neg Formula, Dis1),
    (unary(neg Formula); equivilent(neg Formula); conjunctive(neg Formula); disjunctive(neg Formula)),
    fetch(Formula, Rest, Dis2),
    removeall(neg Formula, Dis1, Temp1),
    removeall(Formula, Dis2, Temp2),
    append(Temp1, Temp2, Newdis),
    removesingle(Dis2, Rest, Newrest),
    not(Rest = Newrest),
    append([Newdis], Newrest, New).

/* usual atomic resolution rule for non-negated */
resolutionstep([Dis1|Rest], New) :-
    member(Atom, Dis1),
    fetch(neg Atom, Rest, Dis2),
    removeall(Atom, Dis1, Temp1),
    removeall(neg Atom, Dis2, Temp2),
    append(Temp1, Temp2, Temp3),
    reduce(Temp3, [], Newdis),
    removesingle(Dis2, Rest, Newrest),
    not(Rest = Newrest),
    append([Newdis], Newrest, New).

/* usual atomic resolution rule for negated */
resolutionstep([Dis1|Rest], New) :-
    member(neg Atom, Dis1),
    fetch(Atom, Rest, Dis2),
    removeall(neg Atom, Dis1, Temp1),
    removeall(Atom, Dis2, Temp2),
    append(Temp1, Temp2, Temp3),
    reduce(Temp3, [], Newdis),
    removesingle(Dis2, Rest, Newrest),
    not(Rest = Newrest),
    append([Newdis], Newrest, New).

resolutionstep([Dis1|Rest], New) :-
    resolutionstep(Rest, Newrest),
    append([Dis1], Newrest, New).
