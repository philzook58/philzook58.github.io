---
author: philzook58
comments: true
date: 2015-11-05 20:49:28+00:00
layout: post
link: https://www.philipzucker.com/da-laser-back-end-baby/
slug: da-laser-back-end-baby
title: Da Laser BACK END BABY
wordpress_id: 238
---

We need to build that back end baby. The butt so to speak. Where the action BE AT.

The idea is to have collaborative aiming of our laser across the internet.

Check it out [https://github.com/ishmandoo/laser](https://github.com/ishmandoo/laser)

So we're gonna docker this. Because we're off the goddamn chain.

Ben already has some code on his github

[https://github.com/ishmandoo/multiplayer_test](https://github.com/ishmandoo/multiplayer_test)

That we're going to modify to our needs. He essentially used

[http://socket.io/get-started/chat](http://socket.io/get-started/chat)/ as a base level + some basic docker

    
    FROM ubuntu
    
    RUN apt-get update
    RUN apt-get install -y nodejs
    RUN apt-get install -y npm
    RUN apt-get install -y git
    RUN git clone https://github.com/ishmandoo/multiplayer_test.git
    RUN cd multiplayer_test && npm install
    
    CMD ["nodejs", "multiplayer_test/server/server.js"]


So this already does what we need it to do basically. Just change the name of the git repository and it'll boot up the server.

check this out [https://www.digitalocean.com/community/tutorials/docker-explained-using-dockerfiles-to-automate-building-of-images](https://www.digitalocean.com/community/tutorials/docker-explained-using-dockerfiles-to-automate-building-of-images) for more deets.





"I built it with  "docker build -t laser ."













and ran it with "docker run -d -p 80:3000 laser""- Ben








Okay, also technically we need a front end too, so

[https://developer.mozilla.org/en-US/docs/Web/API/Touch_events#Create_a_canvas](https://developer.mozilla.org/en-US/docs/Web/API/Touch_events#Create_a_canvas)

duct taped together with the chat application and [http://stackoverflow.com/questions/4037212/html-canvas-full-screen](http://stackoverflow.com/questions/4037212/html-canvas-full-screen) full screening.

We just need to tell the server when touch is down and where. We normalized x and y to be ratios of 0-1 fractions across the screen. It seems we can't rely on not going a little over 1 maybe so be aware.

The Socket.io part is very straightforward.

The express stuffjust serves the ordinary webpages. (app.get)

    
    var express = require('express');
    var app = express();
    var http = require('http').Server(app);
    var io = require('socket.io')(http);
    
    app.get('/', function (req, res) {
      res.sendFile(__dirname + '/client/html/index.html');
    });
    
    app.use('/js', express.static(__dirname + '/client/js'));
    
    
    io.on('connection', function(socket){
      console.log('a user connected');
      socket.pos = {x: 0, y:0}
      socket.touching = false;
      socket.updateTime = 0;
    
    
      socket.on('new pos', function (pos) {
        console.log(pos);
        socket.pos = pos;
        socket.touching = true;
        var date = new Date();
        socket.update_time = date.getTime();
      });
    
      socket.on('no touch', function (data) {
        console.log("no touch");
        socket.touching = false;
      });
    });
    
    app.get('/location', function(req, res){
      var pos = {x: 0, y: 0}
      var x_sum = 0;
      var y_sum = 0;
      var n_touching = 0;
    
    
      var date = new Date();
      var time = date.getTime();
    
      if (io.sockets) {
        var sockets = io.sockets.sockets;
    
        for (i = 0; i < sockets.length; i++) {
          if ((sockets[i].touching) && (time - sockets[i].update_time < 10000)) {
            x_sum += sockets[i].pos.x;
            y_sum += sockets[i].pos.y;
            n_touching++;
          }
        }
      }
    
      if (n_touching > 0){
        pos = {x: x_sum/n_touching, y: y_sum/n_touching}
      }
    
      //res.send(pos.x + ',' + pos.y);
      res.json(pos);
    });
    
    var server = http.listen(3000, function () {
      var host = server.address().address;
      var port = server.address().port;
    
      console.log('Example app listening at http://%s:%s', host, port);
    });


The only thing kind of funky is storing data associated with each client. We just attach it to the socket object, which should be self cleaning to some degree. We also add a timeout just in case we somehow lose a touch end. Maybe unneccessary.

Polling the path /location will return json of the average position of everyone touching the screen.

All in all pretty straightforward. And it seems to work with our phones. Except not Beth.

Now onto the microcontroller code. Should be simple, but for some reason is not. We have to glue together a couple of things if we want to bolt the arduino to an esp8266. Alternatives are to go native on an esp8266 or use a Photon. It is bizarre to me that one of these is not a clear winner. Why is it not so incredibly easy to make http requests on the Photon?

Also, a comment: Being name the photon makes it impossible to search for you. It sounds cool, but it's a bad name.
