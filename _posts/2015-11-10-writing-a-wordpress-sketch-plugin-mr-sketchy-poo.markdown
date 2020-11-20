---
author: philzook58
comments: true
date: 2015-11-10 04:48:58+00:00
layout: post
link: https://www.philipzucker.com/writing-a-wordpress-sketch-plugin-mr-sketchy-poo/
slug: writing-a-wordpress-sketch-plugin-mr-sketchy-poo
title: 'Writing a Wordpress sketch Plugin: Mr. Sketchy-Poo'
wordpress_id: 218
---

So I want to make a plugin that allows me to make quick sketches on my posts.

First I'm going to install a local wordpress on my comp to work with.

Turns out I didn't have mysql installed

    
    brew install mysql




    
    mysql.server start



    
    mysql -uroot
    


Then

    
    CREATE USER 'wordpress'@'localhost' IDENTIFIED BY 'wordpress';


Probably might want to pick a different password or whatever.

    
    CREATE DATABASE wordpress;



    
    GRANT ALL PRIVILEGES ON wordpress . * TO 'wordpress'@'localhost';


Following 5-minute setup guide.

cd into the wordpress folder. Run the following to make a server at 127.0.0.1:8000 in the unzipped wordpress folder

    
    php -S 127.0.0.1:8000 -t .
    


Changed wp-config-sample.php to wp-config.php

and put all my passwords and stuff in there

ERROR ON ESTABLISHING DATABASE CONNECTION

okay.

So I found this script

    
    <?php
    $db = @mysql_connect('127.0.0.1', 'wordpress', 'wordpress');
    if (!$db) echo "connection failed";
    else echo "connection succeeded";
    ?>


and ran it.

Turns out need to replace localhost with 127.0.0.1

I don't know why. Whatevs.

Smooth sailin.

Made my username wordpress and password wordpress. Don't host this for real.

ALRIGHT WE'RE IN.

Installing something by going to a webpage is so goddamn bizarre. I feel like I'm in 1995 or some shit.

php sickens me.

It's fun being a snob! ^o^



Here's some useful looking links

[http://solislab.com/blog/how-to-make-shortcodes-user-friendly/](http://solislab.com/blog/how-to-make-shortcodes-user-friendly/)

[http://stackoverflow.com/questions/2368784/draw-on-html5-canvas-using-a-mouse](http://stackoverflow.com/questions/2368784/draw-on-html5-canvas-using-a-mouse)

[http://www.tinymce.com/wiki.php/Tutorials:Creating_a_plugin](http://www.tinymce.com/wiki.php/Tutorials:Creating_a_plugin)

Okay so the first one seems good but its antiquated

[https://codex.wordpress.org/Plugin_API/Filter_Reference/mce_external_plugins](https://codex.wordpress.org/Plugin_API/Filter_Reference/mce_external_plugins)

Led me here.

The way buttons are made in tinymce has changed. Check out the new way.



I had some trouble getting the mouse to actually draw where it should. I ended up using a recursive travel up through the page to add up all the offsets as seen here.

[http://stackoverflow.com/questions/11444401/perfecting-canvas-mouse-coordinates](http://stackoverflow.com/questions/11444401/perfecting-canvas-mouse-coordinates)

The approach I decided to go with was making a seperate php file that the jquery request will post the image data to.

the wordpress function media_handle_upload can be called on the server side.

[https://codex.wordpress.org/Function_Reference/media_handle_upload](https://codex.wordpress.org/Function_Reference/media_handle_upload)



I didn't realize how hat i also needed to include wp-load.php from the example and was getting weird __() can't be found kind of errors.

This was helpful in packing the images into blobs and the forms in a way that wordpress likes.

http://stackoverflow.com/questions/4998908/convert-data-uri-to-file-then-append-to-formdata

The jquery ajax is quite particular. Apparntly you need to include the lines

    
    	jQuery.ajax({
    				type: 'POST',
    				url:"/wp-content/plugins/myGallery2/upload_image.php",
    				data:formData,
    				contentType: false,
        		processData: false,
    
    				success: function(data){
    					console.log(data);
    					var mytext = "<img src=" + data + "/>"
    					tinyMCE.activeEditor.execCommand('mceInsertContent', 0, mytext);
    				}
    			});


contenttpye false, processdata false in order for it to work.

I just took a wild stab at inserting the image with the img tag and it seems ok.



THIS HAS BEEN A HORRIBLE UNPLEASANT PROJECT.

Find it at [https://github.com/philzook58/mrsketcho](https://github.com/philzook58/mrsketcho)

[![](http://philzucker.nfshost.com/wordpress/wp-content/uploads/2015/11/Mon-Nov-09-2015-234733-GMT-0500-EST.png)](http://philzucker.nfshost.com/wordpress/wp-content/uploads/2015/11/Mon-Nov-09-2015-233813-GMT-0500-EST.png)



BOOOOOOYAAAAAAAHHHH

![](http://philzucker.nfshost.com/wordpress/wp-content/uploads/2015/11/Mon-Nov-09-2015-234836-GMT-0500-EST.png)
