---
author: Philip Zucker
date: 2021-05-19
layout: post
title: 2D Optics Demos in Javascript
---


We've been incredibly impressed and inspired by 
<https://ciechanow.ski/cameras-and-lenses/> by Bartosz Ciechanowski.
He did such an incredible job. And it appears he did it all with raw javascript. Javascript is very freeing once you decide to ignore any kind of build system or awful library. And some of the features of modern javascript are rather nice <https://javascript.info/>.

We had very grandiose plans, but we've gotten bogged down, so I've decided to dump out a post of what we have as a checkpoint. It's nice to know when to give up.

The code for all of these is here <https://github.com/Smung-Institute/infinite-darkness>


To start we made a ray of light bounce off a mirror controlled by a slider.
<https://github.com/Smung-Institute/infinite-darkness/blob/master/mirror.html>
This was built unsytematically as a one off..
<embed type="text/html" src="https://smung-institute.github.io/infinite-darkness/mirror.html" width="600" height="600">

The basic infrastructure for these is as a simple html page with inline javascript using canvas. Here is a template:
```html
<html>
<script>
    var canvas;
    var state = 0;

    draw = (state) => {
        var ctx = canvas.getContext("2d");

        ctx.resetTransform();
        ctx.clearRect(0, 0, canvas.width, canvas.height);

        ctx.fillStyle = "#000000";
        ctx.fillRect(0, 0, canvas.width, canvas.height);

    }

    tick = () => {
        draw(state);
        window.requestAnimationFrame(tick);
    }

    init = (event) => {
        var container = document.getElementById("container")
        canvas = document.createElement("canvas");
        canvas.width = 500;
        canvas.height = 500;
        container.appendChild(canvas)
        window.requestAnimationFrame(tick);
    }

    window.onload = init
</script>

<div class="container" id="container"></div>
<input type="range" min="-8" max="8" value="0" step="0.0001" class="slider" id="slider">

</html>
```

We were initially thinking to make demos explaining interference (double slit etc). This was a demo attempting the start of showing interference via vector addition. It's kind of pleasant looking, but we decided not very educational ultimately.
<https://smung-institute.github.io/infinite-darkness/circles.html>
<embed type="text/html" src="https://smung-institute.github.io/infinite-darkness/circles.html" width="600" height="600">


Some canned wave (we use the closed form solution of the wave coming from a point source) stuff using webgl. <https://github.com/Smung-Institute/infinite-darkness/blob/master/points_webgl.html> Webgl is rather disorienting to use, but it does make this buttery smooth. A very barebones exmaple showing the setup of webgl is here <https://github.com/Smung-Institute/infinite-darkness/blob/master/webgl.html>.

<embed type="text/html" src="https://smung-institute.github.io/infinite-darkness/points_webgl.html" width="600" height="600">

This is the core of the drawing code. We use $\sin(\omega t + kR)/R$ as the field of two point sources that are interfering and draw the squared amplitude.
```C
        void main() {
            float lambda = 0.1;
            float L1 = sqrt( pow(coords.x, 2.0) + pow(coords.y, 2.0));
            float L2 = sqrt(pow(coords.x - 1.0, 2.0) + pow(coords.y - 1.0, 2.0));
            float phi1 = sin((L1 + time) * 2.0 * 3.14 / lambda) / L1;
            float phi2 = sin((L2 + time)  * 2.0 * 3.14 * 2.1 / lambda) / L2;
            float A = pow(phi1 + phi2, 2.0);
            gl_FragColor = vec4(vec3(A), 1);
        }
```

A chunkier version using canvas instead of webgl. Way worse.
<https://smung-institute.github.io/infinite-darkness/points.html>


Then we hit upon the idea of making demos to explain etendue, which has been my white whale for years. Etendue <https://en.wikipedia.org/wiki/Etendue> is a concept in optics that is both the most fundamental and the least taught to the average physicist. It clarifies many things.
Etendue is "ray volume". Rays are parametrized by both an angular direction and position perpendicular to the direction of the ray. Etendue is the product of a solid angle and area a bundle of rays pass through. 


- It is the analog of phase space volume in mechanics.
- It is the conserved. This is the analog of Liouville's theorem
- It increases when light goes through fogged glass for example. This is somewhat like the analog of the increase of entropy in mechanics.
- It explains why you can't use lenses to break the second law of thermo <https://what-if.xkcd.com/145/> (concentrate the light of a blackbody with a lens to make something hotter than the body itself.)
- When Etendue in units of wavelength approaches 1, wave optics becomes important. This is the analog of the Heisenberg uncertainty principle
- It explains numerical aperture <https://en.wikipedia.org/wiki/Numerical_aperture>
- It measures the amount two surfaces are in view of each other. See view factor which is important in radiative trasnfer <https://en.wikipedia.org/wiki/View_factor>
- Etendue is studied extensively in non-imaging optics, where the goal is to collect light to illuminate things
- Point sources do not exist. They always have extent.
- Perfect collimation does not exist. They always have angular spread (because of diffraction).


We made a custom sort of ad hoc aperture demo. We're plotting the angle and vertical offset of the rays, which is the phase space of the rays. This is the analog of a free particle in mechanics.
<https://smung-institute.github.io/infinite-darkness/etendue/rand_lines.html>
<embed type="text/html" src="https://smung-institute.github.io/infinite-darkness/etendue/rand_lines.html" width="600" height="700">

We then went off on a tangent building a 2d ray tracing library for generality so we could have apertures and lenses. It is vaguely based off Ray Tracing in One Weekend <https://raytracing.github.io/>. Going 2D is nice, it simplifies some of the mathematics, and makes it easier to draw and visualize. 

It's a nice little kata to make the basic 2D vector functions. I really rather like the "new" arrow notation for functions in javascript. We are probably overusing it in our zeal though.

```javascript
///////////////////////////
//        Vectors        //
///////////////////////////
V2 = (x, y) => [x, y]
dot = (u, v) => u[0] * v[0] + u[1] * v[1];
norm2 = (u) => dot(u, u);
norm = (u) => Math.sqrt(norm2(u));
vadd = (u, v) => V2(u[0] + v[0], u[1] + v[1]);
smul = (a, u) => V2(a * u[0], a * u[1]);
vsub = (u, v) => V2(u[0] - v[0], u[1] - v[1]);
sdiv = (a, u) => V2(u[0] / a, u[1] / a);
normalize = (u) => sdiv(norm(u), u);
vneg = (u) => smul(-1, u);
cross = (u, v) => u[0] * v[1] - u[1] * v[0];
angle = (u, v) => {
    var u = normalize(u);
    var v = normalize(v);
    return Math.atan2(cross(u, v), dot(u, v));
}
rotate = (theta, v) => V2(Math.cos(theta) * v[0] - Math.sin(theta) * v[1], Math.sin(theta) * v[0] + Math.cos(theta) * v[1])
perp = (v) => V2(-v[1], v[0]);
reflect = (v, n) => vsub(v, smul(2 * dot(v, n), n));
lerp = (r0, r1, t) => vadd(r0, smul(t, vsub(r1, r0)));
```

We represent a ray as a point and direction vector.

```javascript
///////////////////////////
//        Optics         //
///////////////////////////

Ray = (pos, dir) => ({
    pos: pos,
    dir: normalize(dir)
});

prop = (ray, t) => Ray(vadd(ray.pos, smul(t, ray.dir)), ray.dir);

prop_draw = (ray, t, ctx) => {
    var new_ray = prop(ray, t)
    line_artist(ray.pos, new_ray.pos)(ctx)
    return new_ray
}

Hit = (pos, norm, t) => ({
    pos: pos,
    normal: normalize(norm),
    t: t
});


line_collider = (r0, r1) => (ray) => {
    var v1 = vsub(ray.pos, r0);
    var v2 = vsub(r1, r0);
    var v3 = perp(ray.dir);

    var t1 = cross(v2, v1) / dot(v2, v3);
    var t2 = dot(v1, v3) / dot(v2, v3);

    if (0 <= t2 && t2 <= 1 && t1 > 0.001) {
        var normal = normalize(perp(v2));
        if (dot(normal, ray.dir) > 0) {
            normal = vneg(normal);
        }
        return Hit(prop(ray, t1).pos, normal, t1);
    }
    else {
        return null;
    }
}
```

Materials take a `Hit` and change the incoming ray into some new thing, reflecting or refracting it.

```javascript
///////////////////////////
//       Materials       //
///////////////////////////


Objekt = (collider, material, draw) => ({
    collider: collider,
    material: material,
    draw: draw
})

line_source = (r0, r1) => () => {

    var angle = Math.PI * Math.random()

    return Ray(lerp(r0, r1, Math.random()), V2(Math.sin(angle), Math.cos(angle)));
}


shiny_material = (hit, ray) => {
    return Ray(hit.pos, reflect(ray.dir, hit.normal));
}

absorbing_material = (hit, ray) => {
    return null;
}

line_artist = (r0, r1) => (ctx) => {
    ctx.strokeStyle = "#FFFFFF";
    ctx.beginPath();
    ctx.moveTo(...r0);
    ctx.lineTo(...r1);
    ctx.stroke();
}

line_collider = (r0, r1) => (ray) => {
    var v1 = vsub(ray.pos, r0);
    var v2 = vsub(r1, r0);
    var v3 = perp(ray.dir);

    var t1 = cross(v2, v1) / dot(v2, v3);
    var t2 = dot(v1, v3) / dot(v2, v3);

    if (0 <= t2 && t2 <= 1 && t1 > 0) {
        var normal = normalize(perp(v2));
        if (dot(normal, ray.dir) > 0) {
            normal = vneg(normal);
        }
        return Hit(prop(ray, t1).pos, normal, t1);
    }
    else {
        return null;
    }
}

shiny_line = (r0, r1) => {
    return Objekt(
        line_collider(r0, r1),
        shiny_material,
        line_artist(r0, r1)
    )
}

union = (...geoms) => ray => {
    var bestHit = null;
    geoms.forEach(geom => {
        hit = geom(ray);
        if (hit != null) {
            if (bestHit == null || hit.t < bestHit.t) {
                bestHit = hit;
            }
        }
    });
    return bestHit;
}

rect_collider = (x, y, w, h) => union(
    line_collider(V2(x, y), V2(x + w, y)),
    line_collider(V2(x + w, y), V2(x + w, y + h)),
    line_collider(V2(x + w, y + h), V2(x, y + h)),
    line_collider(V2(x, y + h), V2(x, y))
)

boundary = (x, y, w, h) => Objekt(
    rect_collider(x, y, w, h),
    absorbing_material,
    (ctx) => { }
)

absorbing_rect = (x, y, w, h) => Objekt(
    rect_collider(x, y, w, h),
    absorbing_material,
    (ctx) => {
        ctx.beginPath();
        ctx.rect(x, y, w, h);
        ctx.stroke();
    }
)
```


<https://smung-institute.github.io/infinite-darkness/etendue/aperture.html>
<embed type="text/html" src="https://smung-institute.github.io/infinite-darkness/etendue/aperture.html" width="600" height="600">
<embed type="text/html" src="https://smung-institute.github.io/infinite-darkness/etendue/aperture_phase.html" width="600" height="700">
<https://smung-institute.github.io/infinite-darkness/etendue/aperture_phase.html>



### Junk

<https://quazikb.github.io/WaveEq/index.html>


Really nice looking airheads lorenz attractors. Raytraced
<https://twitter.com/tylermorganwall/status/1367488353571078149?s=12>

ray marching ascii. Clever. i had never thought of this.
If you could get the bitmap of characters it might be nice
to getting the hamming distant closest one?
If that even means anything
<https://ch-st.de/its-ray-marching-march/>


What about Purcell radiation example. Wiggle a charge

<https://twitter.com/bencbartlett/status/1369396941730312193?s=12> oncioherent lithgt tweet

<https://rafael-fuente.github.io/visual-explanation-of-the-van-cittert-zernike-theorem-the-double-slit-experiment-with-incoherent-and-coherent-light.html>

<https://github.com/rafael-fuente/Incoherent-Light-Simulation>

<https://developer.mozilla.org/en-US/docs/Web/API/Canvas_API/Tutorial/Pixel_manipulation_with_canvas>

<https://meep.readthedocs.io/en/latest/>


