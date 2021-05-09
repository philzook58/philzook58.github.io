RRAAAAAAAWWWW DOG


We've been incredibly impressed and inspired by 
https://ciechanow.ski/cameras-and-lenses/ 
Bartosz Ciechanowski 
He did such an incredible job. And it appears he did it all with raw javascript

To start we made a ray of light bounce off a mirror controlled by a slider.



https://quazikb.github.io/WaveEq/index.html


Really nice looking airheads lorenz attractors. Raytraced
https://twitter.com/tylermorganwall/status/1367488353571078149?s=12

ray marching ascii. Clever. i had never thought of this.
If you could get the bitmap of characters it might be nice
to getting the hamming distant closest one?
If that even means anything
https://ch-st.de/its-ray-marching-march/


What about Purcell radiation example. Wiggle a charge

https://twitter.com/bencbartlett/status/1369396941730312193?s=12 oncioherent lithgt tweet

https://rafael-fuente.github.io/visual-explanation-of-the-van-cittert-zernike-theorem-the-double-slit-experiment-with-incoherent-and-coherent-light.html

https://github.com/rafael-fuente/Incoherent-Light-Simulation

https://developer.mozilla.org/en-US/docs/Web/API/Canvas_API/Tutorial/Pixel_manipulation_with_canvas

https://meep.readthedocs.io/en/latest/

Question of returning t vs returning
Are there good ray coordinate systems?
projective x y w, but also alpha?


If we treat these ray functions as differentiable, we get gaussian beam optics



ray = (x,y,theta) => ({
    pos : [x,y];
    theta : theta
})

dot = (u,v) => {
    u[0] * v[0] + u[1] * v[1]
}

vadd = (u,v) => { // or zipWith? Not sure javascript has something good for this.
    [ u[0] + v[0] , u[1] + v[1]  ]
}

smul = (s,v) => {  // Or map( l => s*l, v )
    [ s * u[0] ,  ] 
}

norm = u => {
}

setX = x1 => ray => {
    {
        x: x1,
        y: ray.y + (x1 - line.x) * Math.tan(line.theta),
        theta: line.theta
    }
}

setY = similar

translateX = dx => line => {

}

rotate = theta => line => {
    {
        x :  line.x * Math.cos(theta) + line.y * Math.sin(theta);
        y : -line.x * Math.sin(theta) + line.y * Math.cos(theta);
        theta : line.theta + theta
    }
}
translate
scale

We can also make these combinators apply to line transformers by applying the operation and then it's inverse afterwards.
That's kind of fun.


propagate = t => line => {
        ()
            x : line.x + t * Math.cos(theta),
            y : line.y + t * Math.sin(theta),
            theta : line.theta
        })

reflect = (nx,ny) => ray => {
    var rx = Math.cos(ray.theta);
    var ry = Math.sin(ray.theta);
    var d  = nx*rx + ny*ry;
    var rx2 = rx - d * nx;
    var ry2 = ry - d * ny;
    return {
        x : ray.x,
        y : ray.y,
        theta : Math.atan2( rx2, ry2) 
        }
}

Should we use arrays instead of x y components?
And make some vector math.


collision_line = (a,b,c) => line => {
    /* ax + by + c = 0
    x = x0 + tcos(theta)
    y = y0 + tsin(theta)
    a*(x0 + t cos) + b*(y0 + t sin) + c = 0
    t = -(c + a*x0 + b*y1) / (a cos + b sin)
    */
    var t = -(c + a*line.x + b*line.y) / (a * Math.cos(line.theta) + b *Math.sin(line.theta));
    if t >= 0 {
        propagate(t)(line);
    }else{
        return null;
    }
}
collision_circle = (xc,yc,r) => line => {
    /* 
    (x - xc) ** 2 + (y - yx)**2 = r**2
    x = x0 + tcos(theta)
    y = y0 + tsin(theta)
    plug in. t is quadratic equation.
    */
    find smaller positive root.
    }else{
        return null;
    }
}


snell = (nx,ny, n1, n2) => {
    // compute nalge to normal
    // do snell and adjust theta
}

// Collision conic. Parabola

// In some cases it is nice to return t

collide_rect() => {
    t1 = line();
    t2 = line();
    t3 = line();
    t4 = line();
    return minimum(t1,t2,t3,t4)
}

// There might something really good here.
// 2d geometry has all kinds of good stuff right?
collide_polyline =>


aperture = (x,y,d) => line => {
    var line = setX(x)(line);
    if ( y - d < line.y  & line.y < y + d ){
        return line;
    }
    else{
        return null;
    }
}
