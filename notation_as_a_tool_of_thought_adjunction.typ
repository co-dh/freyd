# Notation as a Tool of Thought - Adjunction
Adjunction: F(x)<=y iff x<=G(y),give F, G montonic.

F(x)<=F(x) => x<=G(F(x)) => F(x) <= F(G(F(x)))     
G(y)<=G(y) => F(G(y)<=y  => G(F(G(x))) <= G(y)   

- there are both function application and composition above, we can get rid of applicaiton by replacing x with constanct function X: *->x . F(x) = F.X
- use diagram order F . X => XF 
- replace F with / , G with \
- put a<=b as a over b.
- chagne from X<=XF  to 1<=F

X/ = X
Y    Y\

X/ => X     =   *   ={put \ on left}=> \ 
X/    X/\       /\                     \/\             
                    ={put / on right} =>  /
                                          /\/

Y\ => Y\/  =  \/   ={put / on left}=> /\/
Y\    Y        *                        / 
                   ={put \ on right}=> \/\
                                        \

now we have /\/ = /  and \/\ = \



