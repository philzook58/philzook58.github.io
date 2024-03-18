
```bash
cart : R^3 -> M
cart(_,_,_)

x y z : M -> R

x(cart(X,Y,Z)) = X
y(cart(X,Y,Z)) = Y

cyl(R,T,Z) = cart(Rcos(T), Rsin(T), Z)
cart(X,Y,Z) = cyl(sqrt(X^2 + Y^2), atan2(X,Y), Z)

point : M

dist : M -> M -> R
dist(P1,P2) 

% hyperreals?


a curve.
p : R -> M
p(T) = cart(T,T,0)


%vector derivative
% a rate of change of a function
dp : (M -> R) -> R -> R  % (?)
dp(f)(T) = f'(p(T)) * 2

% vector field
v : (M -> R) -> M -> R




a surface
q : M2 -> M

chart : R^2 -> M2
x(q(chart(X,Y))) =

% exterior deriavtive
d : (M -> R) -> M -> ?

% a different cartersian coordinate system
x(cart'(X,Y,Z)) = x(cart(X,Y,Z)) + a
```

it would be nice for the charts to be partial.
