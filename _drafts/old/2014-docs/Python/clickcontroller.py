

class View:
    def __init__(self,x=0,y=0,width=100,height=100,callonclick=None,owner=None):
        view_id = 0
        self.xpos = x
        self.ypos = y
        self.width = width
        self.height = height

        #function call on click
        self.callonclick = callonclick
        
        #object that you call function on
        self.owner = owner

class Click_Dispatch:
    ViewList = []
    def addView(self,view):
        #add a box to our list
        self.ViewList.append(view)
        
    def dropView(self,view):
        self.ViewList.remove(view)
        #take view off list


        #priority exchanging

    def click(self,x,y):
        #Go through the list, find first object that is in the right spot
        for view in ViewList:
            if x <(view.x + view.width) & x < view.x & \
                y < (view.y + view.height) & y > view.y:

                view.owner.callonclick()
                break

myview = View()
dispatch = Click_Dispatch()

dispatch.addView(myview)
       
    
