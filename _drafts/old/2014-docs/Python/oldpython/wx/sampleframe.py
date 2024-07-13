import wx
app = wx.App(False)
class MyFrame(wx.Frame):
    def __init__(self,parent,title):
        wx.Frame.__init__(self,parent,title=title,size=(200,100))
        self.control = wx.TextCtrl(self,style=wx.TE_MULTILINE)
        self.Show(True)

frame = MyFrame(None,'Text Editor')
app.MainLoop()
    
