import pyglet

window = pyglet.window.Window()
size = 36
def updatelabel():
	label = pyglet.text.Label('Hello, world',
                          font_name='Times New Roman',
                          font_size=size,
                          x=window.width//2, y=window.height//2,
                          anchor_x='center', anchor_y='center')
						  
						 
@window.event
def on_mouse_press(x, y, button, modifiers):
    if button == mouse.LEFT:
        size = size - 3
		updatelabel()
def on_draw():
    window.clear()
    label.draw()
	
pyglet.app.run()

