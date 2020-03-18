?-op(140, fy, neg).
?-op(160, xfy, [and, or, imp, revimp, uparrow, downarrow, notimp, notrevimp, equiv, notequiv]).

/* member(Item,List) :- item occurs in list */
/* checks if formulae are equivilent */
member(X, [X|_]).
member(X, [_|Tail]) :-
    member(X, Tail).

/* memberprime(Formula,List) :- will see if a semantically equivilent formula
                            exists in the list */
memberprime(X, [Head|Tail]) :-
    equivformula(X, Head).
memberprime(X, [_|Tail]) :-
    member(X, Tail).


/* equivlist(List1, List2) :- will identify if the lists are equivilent,
                              meaning they contain all the same elements
                              (not necessarily in the same order though) */

equivlist([],[]).
equivlist([Head|Tail], List2) :-
    member(Head, List2),
    removesingle(Head, List2, Newlist),
    not(Newlist = List2),
    equivlist(Tail, Newlist).

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

/* base case */
removesingle(X, [], []).
/* will only remove the first instance of the X */
removesingle(X, [X|Rest], Y) :-
    Y = Rest.
/* searches for the X in the second list */
removesingle(X, [Head|Rest], Y) :-
    removesingle(X, Rest, Y2),
    append([Head], Y2, Y).



/* append(List1, List2, List3) :- will combine lists 1 and 2 into a single list:
                                  list3 */
append([X|Y],Z,[X|W]) :-
    append(Y,Z,W).
append([],X,X).


/* fetch(Element,Biglist,Return) :- searches through a list of lists to see if
                                    the element exists in any of them. if it
                                    does, return the list with the element
                                    present */
fetch(Element, [List | Rest], Return) :-
    member(Element, List),
    Return = List.
fetch(Element, [_ | Rest], Return) :-
    fetch(Element, Rest, Return).


/* removeall(Item, List, Newlist) :- removes Item from List and produces Newlist */

removeall(X, [], []) :- !.
removeall(X, [X|Xs], Y) :- !, removeall(X, Xs, Y).
removeall(X, [T|Xs], Y) :- !, removeall(X, Xs, Y2), append([T], Y2, Y).

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

/* new equivilence-based operators */

equivilent(_ equiv _).
equivilent(_ notequiv _).
equivilent(neg(_ equiv _)).
equivilent(neg(_ notequiv _)).

/* necessary for immediate check of equivilence */

immediateequiv(_ equiv _).
immediatenotequiv(_ notequiv _).

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
/* new equivilence-based operations */

/* component(X,Y) :- Y is the component of the unary formula X */

component(neg neg X, X).
component(neg true, false).
component(neg false, true).
/* new equivilence-based operations */
component(X equiv Y, (neg X or Y) and (X or neg Y)).
component(neg(X equiv Y), (neg X or neg Y) and (X or Y)).
component(X notequiv Y, (neg X or neg Y) and (X or Y)).
component(neg(X notequiv Y), (neg X or Y) and (X or neg Y)).


/* singlestep(Old,New) :- new is result of applying single step of expansion
                          process to Old, which is a generalised disjunction
                          of generalised conjunctions */

singlestep([Disjunction|Rest], New) :-
    member(Formula, Disjunction),
    unary(Formula),
    component(Formula, Newformula),
    removeall(Formula, Disjunction, Temporary),
    append([Newformula], Temporary, Newdisjunction),
    print("Applying Unary..."), nl,
    New = [Newdisjunction | Rest].

singlestep([Disjunction|Rest], New) :-
    member(Formula, Disjunction),
    equivilent(Formula),
    component(Formula, Newformula),
    removeall(Formula, Disjunction, Temporary),
    append([Newformula], Temporary, Newdisjunction),
    print("Applying Equiv..."), nl,
    New = [Newdisjunction | Rest].


singlestep([Disjunction|Rest], New) :-
    member(Alpha, Disjunction),
    conjunctive(Alpha),
    components(Alpha, Alphaone, Alphatwo),
    removeall(Alpha, Disjunction, Temporary),
    append([Alphaone], Temporary, Newdisone),
    append([Alphatwo], Temporary, Newdistwo),
    print("Applying Alpha..."), nl,
    New = [Newdisone, Newdistwo | Rest].

singlestep([Disjunction|Rest], New) :-
    member(Beta, Disjunction),
    disjunctive(Beta),
    components(Beta, Betaone, Betatwo),
    removeall(Beta, Disjunction, Temporary),
    Newdis = [Betaone, Betatwo | Temporary],
    print("Applying Beta..."), nl,
    New = [Newdis | Rest].

singlestep([Disjunction|Rest], New) :-
    singlestep(Rest, Newrest),
    /* requires this as otherwise Newrest was wrapped in a list, so this fixes
       thing being too wrapped in objects */
    append([Disjunction], Newrest, New).


/* prove(Old,New) :- New is result of applying singlestep as many times as
                      possible on Old */

prove(Con) :-
    reduceall(Con, [], Tempcon),
    nl,print("Attempting resolution..."), print(Tempcon), nl,
    resolution(Tempcon),
    print("Just resolved...."), print(Tempcon), nl.

prove(Con) :-
    nl,print("Con is...."), print(Con), nl,
    singlestep(Con, Temp),
    !,
    print("Just took a step...."), print(Temp), nl,
    prove(Temp).


/* resolution(X,Y) :- */

/* true when the empty list is present after rules applied */
resolution(Res) :-
    member([], Res).
/* recurses until empty list or exhausts options */
resolution(Res) :-
    resolutionstep(Res, Temp),
    resolution(Temp).

/* resolutionstep(Old,New) :- new is result of applying single step of
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
    /*print("a-removing: "), print(Atom), nl,
    print("a-Dis1: "), print(Dis1), print(" becomes: "), print(Temp1), nl,
    print("a-Dis2: "), print(Dis2), print(" becomes: "), print(Temp2), nl,
    print("a-Newdis: "), print(Newdis), nl,*/
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
    /*print("b-removing: "), print(Atom), nl,
    print("b-Dis1: "), print(Dis1), print(" becomes: "), print(Temp1), nl,
    print("b-Dis2: "), print(Dis2), print(" becomes: "), print(Temp2), nl,
    print("b-Newdis: "), print(Newdis), nl,*/
    append([Newdis], Newrest, New).

/* recurse case to allow inner elements to be dealt with */
resolutionstep([Dis1|Rest], New) :-
    resolutionstep(Rest, Newrest),
    append([Dis1], Newrest, New).


/* test(Formula) :- will print YES is formula is a tautology, NO otherwise */

/* cases for when immediately obvious it's provable to prevent large searches */
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

/* usual test call, where immidiate observation not encountered */
test(Formula) :-
    if_then_else(prove([[neg Formula]]), print("YES"), print("NO")).

temp(Formula) :-
    clauseform(neg Formula, CNF),
    print("CNF: "), print(CNF), nl,
    reduceall(CNF, [], NewCNF),
    /* cut to prevent backtracking */
    !,
    print("NewCNF: "), print(NewCNF), nl,
    if_then_else(resolution(NewCNF, Resolve), print("YES"), print("NO")).


/* if_then_else(A,B,C) :- if A holds then perform B, otherwise perform C */
if_then_else(A, B, C) :-
    A,
    !,
    B.

if_then_else(A, B, C) :-
    C.

/* strip(Formula, X, Y) :- breaks down formulae into atomic parts, only for
                           those where the order of the variables does not
                           matter */

strip(X equiv Y, X, Y).
strip(X notequiv Y, X, Y).
strip(X and Y, X, Y).
strip(X or Y, X, Y).
strip(X uparrow Y, X, Y).
strip(X downarrow Y, X, Y).

/* equivformula(Formulaone,Formulatwo) :- will compare each formula to see if
                                          they are sematically equivilent */

/* strips away neg cases */
equivformula(neg Formulaone, neg Formulatwo) :-
    equivformula(Formulaone, Formulatwo).
/* deals with comparing atomic values */
equivformula(Atomone, Atomtwo) :-
    Atomone == Atomtwo.
/* breaks down larger formulae */
equivformula(Formulaone, Formulatwo) :-
    strip(Formulaone, X1, Y1),
    strip(Formulatwo, X2, Y2),
    ((equivformula(X1, X2), equivformula(Y1, Y2));
     (equivformula(X1, Y2), equivformula(Y1, X2))).
