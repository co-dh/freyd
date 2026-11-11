# The Wumpus world

    obj C = {11,12,13,14,21,22,23,24,31,32,33,34,41,42,43,44}   -- the cells [x,y], written xy
    obj N = 0…5                                   -- the steps of the route

    a : C ⟶ C ≜ {(11,12),(12,13),(13,14),(21,22),(22,23),(23,24),(31,32),(32,33),(33,34),(41,42),(42,43),(43,44),(11,21),(21,31),(31,41),(12,22),(22,32),(32,42),(13,23),(23,33),(33,43),(14,24),(24,34),(34,44)}   -- each cell to the next along a column or a row
    adj : C ⟶ C ≜ a ∪ a°                          -- the cells beside each cell

The views of one KB: V visited, B breeze, S stench; R(𝟙 − X) keeps the rows of R whose value is not in X.

    uniq(R : α ⟶ β) : α ⟶ β ≜ R ∩ (R°\𝟙)         -- the rows whose key has one value
    noB(V : C ⟶ C, B : C ⟶ C) : C ⟶ C ≜ V(𝟙 − B)
    noPit(V : C ⟶ C, B : C ⟶ C) : C ⟶ C ≜ V ∪ ran(noB(V,B) adj)
    cand(V : C ⟶ C, B : C ⟶ C) : C ⟶ C ≜ B adj(𝟙 − noPit(V,B))
    pit(V : C ⟶ C, B : C ⟶ C) : C ⟶ C ≜ ran(uniq(cand(V,B)))
    noS(V : C ⟶ C, S : C ⟶ C) : C ⟶ C ≜ V(𝟙 − S)
    noW(V : C ⟶ C, S : C ⟶ C) : C ⟶ C ≜ V ∪ ran(noS(V,S) adj)
    wmay(S : C ⟶ C) : 1 ⟶ C ≜ S⊤ \ adj           -- the cells beside every stench
    wcand(V : C ⟶ C, S : C ⟶ C) : 1 ⟶ C ≜ wmay(S)(𝟙 − noW(V,S))
    wumpus(V : C ⟶ C, S : C ⟶ C) : C ⟶ C ≜ ran(uniq(wcand(V,S)))
    noWumpus(V : C ⟶ C, S : C ⟶ C) : C ⟶ C ≜ 𝟙 − ran(wcand(V,S))
    safe(V : C ⟶ C, B : C ⟶ C, S : C ⟶ C) : C ⟶ C ≜ noPit(V,B) ∩ noWumpus(V,S)
    frontier(V : C ⟶ C) : C ⟶ C ≜ ran(V adj)(𝟙 − V)
    next(V : C ⟶ C, B : C ⟶ C, S : C ⟶ C) : C ⟶ C ≜ frontier(V) ∩ safe(V,B,S)

The world and the route walked through it.

    pits : C ⟶ C ≜ {(31,31),(33,33),(44,44)}
    w : C ⟶ C ≜ {(13,13)}                         -- the wumpus
    g : C ⟶ C ≜ {(23,23)}                         -- the gold
    route : N ⟶ C ≜ {(0,11),(1,21),(2,11),(3,12),(4,22),(5,23)}   -- the cell of each step

The KB after each step, a family N ⟶ C×C: the route's cells up to step k where the percept p held.

    K(p : C ⟶ α) : N ⟶ α×α ≜ ((route p)°≤)°⟨𝟙,𝟙⟩
    V : N ⟶ C×C ≜ K(𝟙)
    B : N ⟶ C×C ≜ K(dom(adj pits))                -- breeze beside a pit
    S : N ⟶ C×C ≜ K(dom(adj w))                   -- stench beside the wumpus
    G : N ⟶ C×C ≜ K(g)                            -- glitter on the gold

    print next(V,B,S)
