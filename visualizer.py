import cairo

# Draw a transistor with its polysilicon gate
# Inputs:
#   is_pmos: True if PMOS. False otherwise
#   x: X-coordinate of the top-left corner of the diffusion area
#   y: Y-coordinate of the top-left corner of diffusion area
#   width: Width of diffusion area
#   length: Length of diffusion area
#   poly_width: Width of polysilicon gate
#   poly_extension: Size in nm of how much after the diffusion area the polysilicon gate will extend
class Transistor(object):
    def __init__(self, is_pmos, x, y, width, length, poly_width, poly_extension):
        self.is_pmos = is_pmos
        self.x = x
        self.y = y
        self.width = width
        self.length = length
        self.poly_width = poly_width
        self.poly_extension = poly_extension

        self.pmos_color = (0, 102, 255, 1)
        self.nmos_color = (0, 204, 0, 1)
        self.poly_color = (255, 51, 0, 1)

    def draw(self, context: cairo.Context) -> None:
        if self.is_pmos:
            context.set_source_rgba(0, (102/255), 1, 1)
        else:
            context.set_source_rgba(0, (204/255), 0, 1)

        context.rectangle(self.x, self.y, self.length, self.width)
        context.fill()

        context.set_source_rgba(1, 51/255, 0, 1)
        context.rectangle(((self.length - self.poly_width) / 2) + self.x, self.y - self.poly_extension, self.poly_width, self.width + (self.poly_extension*2))
        context.fill()


# Plots die into a PNG image
# Inputs:
#   canvas_width: Width of output image in pixels
#   canvas_height: Height of output image in pixels
class Plotter(object):
    def __init__(self, canvas_width, canvas_height):
        self.canvas_width = canvas_width
        self.canvas_height = canvas_height

        self.surface = cairo.ImageSurface(cairo.FORMAT_ARGB32, self.canvas_width, self.canvas_height)
        self.context = cairo.Context(self.surface)
        self.context.set_source_rgb(1, 1, 1)
        self.context.paint()

        # ASAP7 Design Rules
        self.GATE_ACTIVE_EX_1 = 4
        self.GATE_ACTIVE_EX_2 = 25
        self.ACTIVE_W_1 = 27
        self.ACTIVE_S_1 = 27
        self.poly_width = 20
        self.diffusion_length = self.poly_width + self.GATE_ACTIVE_EX_2 + self.GATE_ACTIVE_EX_2

    # Adds transistor to image
    # Inputs:
    #   is_pmos: True if PMOS. False otherwise
    #   column: Column value of transistor placement
    #   row: Row value of transistor placement
    #   width: Diffusion area width (1, 2, or 3)
    def addTransistor(self, is_pmos, column, row, width):
        transistor = Transistor(is_pmos=is_pmos, x=column*self.diffusion_length, y=(row*4*self.ACTIVE_S_1)+self.GATE_ACTIVE_EX_1, width=(width*self.ACTIVE_W_1), length=self.diffusion_length, poly_width=self.poly_width, poly_extension=self.GATE_ACTIVE_EX_1)
        transistor.draw(self.context)

    # Saves die into an image
    # Inputs:
    #   filename: Name of output file with .png extension
    def saveImage(self, filename):
        self.surface.write_to_png(filename)

def tryvisualizer():
    plotter = Plotter(canvas_width=2000, canvas_height=2000)
    plotter.addTransistor(is_pmos=True, column=0, row=0, width=1)
    plotter.addTransistor(is_pmos=True, column=1, row=0, width=2)
    plotter.addTransistor(is_pmos=True, column=2, row=0, width=1)
    plotter.addTransistor(is_pmos=True, column=3, row=0, width=1)
    plotter.addTransistor(is_pmos=True, column=4, row=0, width=3)

    plotter.addTransistor(is_pmos=False, column=0, row=1, width=1)
    plotter.addTransistor(is_pmos=False, column=1, row=1, width=2)
    plotter.addTransistor(is_pmos=False, column=2, row=1, width=1)
    plotter.addTransistor(is_pmos=False, column=3, row=1, width=1)
    plotter.addTransistor(is_pmos=False, column=4, row=1, width=3)
    plotter.saveImage("layout.png")

if __name__ == "__main__":
  tryvisualizer()