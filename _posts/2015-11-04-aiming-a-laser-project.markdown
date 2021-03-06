---
author: philzook58
comments: true
date: 2015-11-04 23:21:45+00:00
layout: post
link: https://www.philipzucker.com/aiming-a-laser-project/
slug: aiming-a-laser-project
title: Aiming a Laser Project
wordpress_id: 234
---

So we hot glued two servos together and the to a mirror.

We're aiming a laser at it. A blindingly powerful laser

Essentially Servo B controls the angle in the x-y plane of the mirror and servo A controls the z angle to that plane.

The mirror law is $ v_2=v_1 - 2(v_1 \cdot n)n$

Where all are unit vectors. $ v_1$ is the incoming, $ n$ is the mirror normal and $ v_2$ is the outgoing unit vector.

We fixed the laser to the base so

$ v_1 = \hat{y}$

The outgoing ray must hit the ceiling (at a height R) at position x,y.

$ v_2 = (x,y,R) \frac {1} {\sqrt{x^2+y^2+R^2}}$

Here's a nice observation:

$ v_2 - \hat{y} \propto n$

So we have an algorithm for finding n right there. Find v2, subtract off 1 and then normalize the resulting vector to get $ \hat{n}$.

Then finally we can write n in terms of the angles $ \alpha,\beta$, which heavily depend on our conventions of where angle 0 is and whether the servo spin clockwise or counterclockwise.

I believe ours came out to be something like:

$ n = (\cos(\alpha)\sin(\beta), -\cos(\alpha)\cos(\beta) ,\sin(\alpha))$

In all honesty, we coded her up, then fiddled with minus signs until it was working. Not necessarily a bad way of going about things. Find the things to think about and find the things to just try.

Then here is the code:

    
    #include <Servo.h>
    #define ARATIO 425/(PI/4)
    #define AZERO 1595
    //#define AZERO 2020
    #define BZERO 1585
    #define D 200.
    
    Servo servoA, servoB;  // create servo object to control a servo
    int v = 0;
    int sign = 1;
    float x = 0.;
    float y = 0.;
    float x_temp;
    float y_temp;
    
    void setup()
    {
      servoA.attach(9);
      servoB.attach(10);  // attaches the servo on pin 9 to the servo object
      move('a',0);
      move('b',0);
      Serial.begin(9600);
    }
    
    
    void loop() {
      // put your main code here, to run repeatedly:
      
      
      if ( Serial.available()) {
        char ch = Serial.read();
        
        switch(ch) {
          case '0'...'9':
          //Pretty goddamn clever right here. Not mine.
            v = v * 10 + ch - '0';
          break;
          case '-':
          //Pretty goddamn clever right here. This time ours.
            sign *= -1;
          break;
          case 'a':
            move('a',v*sign);
            resetV();
          break;
          case 'b':
            move('b',v*sign);
            resetV();
          break;
          case 'x':
            x_temp = float(v*sign);
            moveLineXY(x_temp ,y,100);
            x = x_temp;
            resetV();
          break;
          case 'y':
            y_temp = float(v*sign);
            moveLineXY(x ,y_temp,100);
            y = y_temp;
            resetV();
          break;
          default:
            Serial.write("...the fuck is that?");
            resetV();
          break;
        }
      }
    }
    
    void resetV() {
      sign = 1;
      v = 0;
    }
    
    
    void move(char ch, float angle) {
      switch(ch) {
        case 'a':
          servoA.writeMicroseconds(floor(angle*ARATIO) + AZERO);
        break;
        case 'b':
          servoB.writeMicroseconds(floor(angle*ARATIO) + BZERO);
        break;
        
      }
    }
    
    void moveLineXY(float end_x, float end_y, int n_steps) {
      float start_x = x;
      float start_y = y;
      
      float delta_x = (end_x - start_x)/n_steps;
      float delta_y = (end_y - start_y)/n_steps;
      
      for (int i = 0; i < n_steps; i++) {
        moveXY(start_x + (delta_x * i), start_y + (delta_y * i));
        delay(10);
      }
    }
    
    void moveXY(float x, float y) {
      Serial.println(x);
      Serial.println(y);
      float r = getNorm(x,y,D);
      float vx = x/r;
      float vy = y/r;
      float vz = D/r;
      
      float nx = vx;
      float ny = vy - 1;
      float nz = vz;
     
      float nnorm = getNorm(nx,ny,nz);
      nx = nx/nnorm;
      ny = ny/nnorm;
      nz = nz/nnorm;
      
      float alpha = asin(nz);
      //float phi = atan2(y,x);
      float beta = atan2(nx,-ny);
      
      /*
      if (phi > PI/2) {
        phi = phi - PI;
        theta = theta * -1;
      } else if (phi < -PI/2) {
        phi = phi + PI;
        theta = theta * -1; 
      }
      */
      
      Serial.println(alpha);
      Serial.println(beta);
      
      move('a',alpha);
      move('b',-beta);
    }
    
    float getNorm(float x, float y, float z) {
      return sqrt(sq(x) + sq(y) + sq(z));
    }





