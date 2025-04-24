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
    def __init__(self, is_pmos, x, y, base_width, width_multiplier, length):
        self.is_pmos = is_pmos
        self.x = x
        self.y = y
        self.width = base_width * width_multiplier
        self.base_width = base_width
        self.length = length

        self.pmos_color = (0, 102, 255, 1)
        self.nmos_color = (0, 204, 0, 1)
        self.poly_color = (255, 51, 0, 1)

    def draw(self, context: cairo.Context) -> None:
        if self.is_pmos:
            context.set_source_rgba(0, (102/255), 1, 1)
            context.rectangle(self.x, self.y, self.length, self.width)
        else:
            context.set_source_rgba(0, (204/255), 0, 1)
            context.rectangle(self.x, self.y+(self.base_width*3 - self.width), self.length, self.width)

        context.fill()


# Plots die into a PNG image
# Inputs:
#   canvas_width: Width of output image in pixels
#   canvas_height: Height of output image in pixels
class Plotter(object):
    def __init__(self, result, sites, rows):
        self.result = result
        self.sites = sites
        self.rows = rows

        # ASAP7 Design Rules
        self.GATE_ACTIVE_EX_1 = 4
        self.GATE_ACTIVE_EX_2 = 25
        self.ACTIVE_W_1 = 27
        self.ACTIVE_S_1 = 27
        self.poly_width = 20
        self.diffusion_length = self.poly_width + self.GATE_ACTIVE_EX_2 + self.GATE_ACTIVE_EX_2

        self.surface = cairo.ImageSurface(cairo.FORMAT_ARGB32, self.diffusion_length*self.sites, 8*self.ACTIVE_S_1*self.rows)
        self.context = cairo.Context(self.surface)
        self.context.set_source_rgb(1, 1, 1)
        self.context.paint()

    # Adds transistor to image
    # Inputs:
    #   is_pmos: True if PMOS. False otherwise
    #   column: Column value of transistor placement
    #   row: Row value of transistor placement
    #   width: Diffusion area width (1, 2, or 3)
    def addTransistor(self, is_pmos, column, row, width):
        transistor = Transistor(is_pmos=is_pmos, x=column*self.diffusion_length, y=(row*4*self.ACTIVE_S_1)+self.GATE_ACTIVE_EX_1, base_width = self.ACTIVE_W_1, width_multiplier=width, length=self.diffusion_length)
        transistor.draw(self.context)

    # Draws polysilicon gate on top of transistor pair
    # Inputs:
    #   column: Column value of transistor pair
    #   row: Row value of transistor pair
    #   context: Cairo context
    def drawPoly(self, column, row, context: cairo.Context):
        context.set_source_rgba(1, 51 / 255, 0, 1)
        context.rectangle(((self.diffusion_length - self.poly_width) / 2) + column*self.diffusion_length, (row*8*self.ACTIVE_S_1),
                          self.poly_width, (7*self.ACTIVE_S_1)+(self.GATE_ACTIVE_EX_1*2))
        context.fill()

    # Draws transistor pair into image with polysilicon gate
    # Inputs:
    #   column: Column value of transistor pair
    #   row: Row value of transistor pair
    #   pmos_width: Diffusion area width of PMOS transistor (0, 1, 2, or 3)
    #   nmos_width: Diffusion area width of NMOS transistor (0, 1, 2, or 3)
    def addTransistorPair(self, column, row, pmos_width, nmos_width):
        if (pmos_width > 0):
            self.addTransistor(True, column, row*2, pmos_width)

        if (nmos_width > 0):
            self.addTransistor(False, column, (row*2)+1, nmos_width)

        self.drawPoly(column, row, self.context)

    def plot(self):
        for r in range(self.result.num_rows):
            for s in range(self.result.num_sites):
                print(r, s)
                print('result block: ', self.result.pmos_cell_at(r,s))
                print(self.result.pmos_cell_at(r, s).get_width(), self.result.nmos_cell_at(r, s).get_width(), "\n\n")
                self.addTransistorPair(column=s, row=r, pmos_width=self.result.pmos_cell_at(r, s).get_width(), nmos_width=self.result.nmos_cell_at(r, s).get_width())

    # Saves die into an image
    # Inputs:
    #   filename: Name of output file with .png extension
    def saveImage(self, filename):
        self.surface.write_to_png(filename)

def tryvisualizer():
    plotter = Plotter(canvas_width=2000, canvas_height=2000)

    plotter.addTransistorPair(column=0, row=0, pmos_width=1, nmos_width=1)
    plotter.addTransistorPair(column=1, row=0, pmos_width=2, nmos_width=2)
    plotter.addTransistorPair(column=2, row=0, pmos_width=1, nmos_width=1)
    plotter.addTransistorPair(column=3, row=0, pmos_width=1, nmos_width=1)
    plotter.addTransistorPair(column=4, row=0, pmos_width=3, nmos_width=3)

    plotter.addTransistorPair(column=6, row=0, pmos_width=1, nmos_width=1)
    plotter.addTransistorPair(column=7, row=0, pmos_width=2, nmos_width=2)
    plotter.addTransistorPair(column=8, row=0, pmos_width=1, nmos_width=1)
    plotter.addTransistorPair(column=9, row=0, pmos_width=1, nmos_width=1)
    plotter.addTransistorPair(column=10, row=0, pmos_width=3, nmos_width=3)

    plotter.addTransistorPair(column=0, row=1, pmos_width=1, nmos_width=1)
    plotter.addTransistorPair(column=1, row=1, pmos_width=2, nmos_width=2)
    plotter.addTransistorPair(column=2, row=1, pmos_width=1, nmos_width=1)
    plotter.addTransistorPair(column=3, row=1, pmos_width=1, nmos_width=1)
    plotter.addTransistorPair(column=4, row=1, pmos_width=3, nmos_width=3)
    plotter.addTransistorPair(column=5, row=1, pmos_width=2, nmos_width=3)
    plotter.addTransistorPair(column=6, row=1, pmos_width=1, nmos_width=1)
    plotter.addTransistorPair(column=7, row=1, pmos_width=2, nmos_width=2)
    plotter.addTransistorPair(column=8, row=1, pmos_width=1, nmos_width=1)
    plotter.addTransistorPair(column=9, row=1, pmos_width=1, nmos_width=1)
    plotter.addTransistorPair(column=10, row=1, pmos_width=3, nmos_width=3)
    plotter.saveImage("layout.png")

if __name__ == "__main__":
  tryvisualizer()