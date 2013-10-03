#!/usr/bin/env python
"""
A graphical user interface that supports the basic functions of pymatgen, including..

References:

Shyue Ping Ong, William Davidson Richards, Anubhav Jain, Geoffroy Hautier,
 Michael Kocher, Shreyas Cholia, Dan Gunter, Vincent Chevrier, Kristin A. Persson, 
 erbrand Ceder. Python Materials Genomics (pymatgen) : A Robust, 
 Open-Source Python Library for Materials Analysis.
 Computational Materials Science, 2013, 68, 314–319. doi:10.1016/j.commatsci.2012.10.028

Menubar:

    File:
        open
        save
        save as
    Edit:
        cut
        copy 
        paste
    Material Genie:
        Analyze VASP output directory tree- Extract computed properties from a VASP run tree using vasprun.xml files
        Analyze VASP output directory tree for ion magnetization- Extract computed properties for ion magnetization from a VASP run tree using vasprun.xml files
        Find Space Group, from POSCAR, CSSR, cif, or vasprun.xml- Find space group symmetry

buttons:

    Plot:
        Plot XMU.dat- Plot feff cross section
        Plot LDOS from FEFF LDOS00.dat file:
            Site- Plot feff LDOS density of states by site
            Element- Plot feff LDOS density of states by element
            Orbital- Plot feff LDOS density of states by orbital
        Plot DOS from vasprun.xml file:
            Site- Plot feff DOS density of states by site
            Element- Plot feff DOS density of states by element
            Orbital- Plot feff DOS density of states by orbital
        Plot Charge integration-  Plot charge integration
    View structure- visualization of selected structure
    Clear graph- clear graph
    Exit- destroy GUI window
    
    Find Materials- List materials from MP database using formula or elements
    Get Structure- Gets material structure object using material ID from MP database
    Browse- From file dialog opens a filename
    Create a feff.inp file:
        message box: Enter symbol of absorbing atoms
            Radio button- XANES or EXAFS
            Submit- converts structure to feff.inp file
            Cancel- destroys message box
    Display Structure- Displays structure summary
    Clear text- Clear text
    Exit- destroy GUI window
"""
from __future__ import division

__author__ = "Megan LaRue"
__credits__ = "Alan Dozier, Shyue Ping Ong, Anubhav Jain"
__copyright__ = "Copyright 2011, The Materials Project"
__version__ = "1.2"
__maintainer__ = "Megan LaRue"
__email__ = "meganlarue79@gmail.com"
__status__ = "Beta"
__date__ = "August 12, 2013"


from pymatgen.util.plotting_utils import get_publication_quality_plot
from pymatgen.io.feffio_set import *
from pymatgen.io.feffio import *
from pymatgen.io.vaspio import *
from pymatgen.io.smartio import read_structure, write_structure
from pymatgen.io.cifio import CifParser, CifWriter
from pymatgen.core.structure import Structure, Site, PeriodicSite

from collections import OrderedDict
from pymatgen.io.feffio import FeffLdos
from pymatgen.electronic_structure.plotter import DosPlotter
from pymatgen.electronic_structure.core import Spin
from pymatgen.vis.structure_vtk import StructureVis
#from pymatgen.io.vaspio import Outcar, Vasprun, Chgcar


import matplotlib
import pymatgen.matproj.rest as mp
matplotlib.use('TkAgg')

#from numpy import arange, sin, pi
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg, NavigationToolbar2TkAgg
from matplotlib.figure import Figure
from matplotlib.font_manager import FontProperties

matgenie_dir='/home/meganl/ENV/lib/python2.7/site-packages/pymatgen/scripts/matgenie.py'


import CifFile
import abc

from Tkinter import *
import tkMessageBox

from PIL import Image
from PIL import ImageTk

import Tkinter as Tk
import sys
import os
import subprocess
import tkFileDialog

import ConfigParser
import itertools
import math
import numpy as np
import vtk

from pymatgen.util.coord_utils import in_coord_list
from pymatgen.core.periodic_table import Specie
from pymatgen.core.structure_modifier import SupercellMaker
from pymatgen.core.structure import Structure


import matgenie
root = Tk.Tk() #set Tk to root window (tree hierarchy) p.312

#all the packages imported to run software
            
#########################################################################################################

class Graph(Tk.Frame):
    """
    Creates a graphical visualization of the basic functions of pymatgen
    """
    
    
    def __init__(self,master): #initialize constructor method (automatically invoked)
        """
        Initialize constructor method will automatically invoked the GUI frames including buttons and graph canvas
        
        Args:
            master:
                In Tkinter, master is a toplevel window manager and contains a given widgets
        """
        
        
        Tk.Frame.__init__(self, master, bd = 2) #bd means borderwidth
        
        self.pack() #pack geometry manager-automatically places widgets in frame (rows and columns)
            
        #create a button frame
        
        frame = Frame(root) #row of buttons
        frame.pack(anchor=NW) #row of buttons
        
        self.xmu_ent = Tk.Entry(frame)
        
        #create buttons        
        mbutton = Menubutton(frame, text='Plot')
        picks = Menu(mbutton)
        submenu2 = Menu(mbutton)
        submenu = Menu(mbutton)
        mbutton.config(menu=picks)
        picks.add_command(label ='plot XMU.dat', command = self.plotXMU)
        
        picks.add_cascade(label ='Plot LDOS from FEFF LDOS00.dat file', menu=submenu2)
        
        submenu2.add_command(label = 'DOS by site', command = self.test_ldos_site)
        submenu2.add_command(label = 'DOS by element', command = self.test_ldos_element)
        submenu2.add_command(label = 'DOS by orbital', command = self.test_ldos_orbital)
        
        
        picks.add_cascade(label = 'Plot DOS from vasprun.xml file', menu=submenu)
        
        submenu.add_command(label = 'DOS by site', command = self.test_dos_site)
        submenu.add_command(label = 'DOS by element', command = self.test_dos_element)
        submenu.add_command(label = 'DOS by orbital', command = self.test_dos_orbital)
        
        picks.add_command(label ='Plot Charge integration', command = self.plotchgint)
        
        mbutton.pack(side = LEFT, fill = BOTH, expand = 1)
        mbutton.config(bd=2, relief=RAISED) 
        
        mbutton2 = Menubutton (frame, text = 'View 3D structure')
        picks2 = Menu(mbutton2)
        mbutton2.config(menu=picks2)
        picks2.add_command(label ='view structure from file', command = self.view_structure)
        picks2.add_command(label ='view loaded structure', command = self.view_current_structure)
        
        mbutton2.pack(side = LEFT, fill = BOTH, expand = 1)
        mbutton2.config(bd=2, relief=RAISED)
        
#        b6 = Button(frame, text = 'view structure', command = self.view_structure)
#        b6.pack(side = LEFT, fill = BOTH, expand = 1)
        
        b3 = Button(frame, text = 'Clear graph', command = self.clear_graph)
        b3.pack(side = LEFT, fill=BOTH, expand =1)
        
        b4 = Button(frame, text = 'Exit', command = self._quit)
        b4.pack(side = LEFT, fill=BOTH, expand=1)
        
        #create file import
        self.file_opt = option = {}
        option['defaultextension'] = '.dat'
        option['filetypes'] = [('all files', '.*'), ('feff XMU.dat files', '*.dat')]
        option['initialdir'] = '../test_files'
        option['initialfile'] = ''
        option['parent'] = root
        option['title'] = 'Select file'
        
        #create graph and tool bar
        f = Figure(figsize=(5,4), dpi=100)
        self.plt = f.add_subplot(111)
        self.color_order = ['r', 'b', 'g', 'c', 'k', 'm', 'y']
        self.fontp=FontProperties()
        
        self._doses = OrderedDict()
        self.all_dos = OrderedDict()
        self.stack = False
        self.zero_at_efermi = True
        
        
        self.canvas = FigureCanvasTkAgg(f, master=root)
        #self.canvas.show()
        self.canvas.get_tk_widget().pack(side=Tk.LEFT, fill=Tk.BOTH, expand=1)
        
        self.toolbar = NavigationToolbar2TkAgg( self.canvas, root )
        self.toolbar.update()
        self.canvas._tkcanvas.pack(side=Tk.LEFT, fill=Tk.BOTH, expand=1, padx = 5)
        
    def test_ldos_site(self):
        """
        Calls graph.feff_ldos with site -s option to plot ldos by sites in structure
        """
        option = '-s'
        Graph.feff_ldos(gra, option)
        
    def test_ldos_element(self):
        """
        Calls graph.feff_ldos with site -e option to plot ldos by elements in structure
        """
        option = '-e'
        Graph.feff_ldos(gra, option)
        
    def test_ldos_orbital(self):
        """
        Calls graph.feff_ldos with site -o option to plot ldos by orbital in structure
        """
        option = '-o'
        Graph.feff_ldos(gra, option)
        
    def test_dos_site(self):
        """
        Calls graph.dos_plot with site -s option to plot dos by sites in structure
        """
        option = '-s'
        Graph.dos_plot(gra, option)
        
    def test_dos_element(self):
        """
        Calls graph.dos_plot with site -e option to plot dos by elements in structure
        """
        option = '-e'
        Graph.dos_plot(gra, option)
    
    def test_dos_orbital(self):
        """
        Calls graph.dos_plot with site -o option to plot dos by orbital in structure
        """
        option = '-o'
        Graph.dos_plot(gra, option)

        
    def plotXMU(self):
        """
        Plot feff cross section from xmu.dat files
        """
        file_name=tkFileDialog.askopenfilename(**self.file_opt)
        if file_name == '' or file_name==():
            return
        self.xmu_ent.delete(0, END)
        self.xmu_ent.insert(0, file_name)
        #plot
        file_type = file_name.split(".")[-1]
        if file_type == 'dat':
            
            xmufile = self.xmu_ent.get()
            directory = ''
            directory_list = xmufile.split('/')
            for dir in directory_list[:-1]:
                directory = directory + '/' +dir
            directory = directory[1:]       
            feffinpfile = directory + '/feff.inp'
        
    
         
            xmu = Xmu.from_file(xmufile, feffinpfile)
            
            data = xmu.to_dict
            
            x = data['energies']
            y = data['scross']
            tle = 'Single ' + data['atom'] + ' ' + data['edge'] + ' edge'
            self.plt.plot(x, y, self.color_order[1 % 7], label=tle)
            
            y = data['across']
            tle = data['atom'] + ' ' + data['edge'] + ' edge in ' + data['formula']
            self.plt.plot(x, y, self.color_order[2 % 7], label=tle)
            self.plt.set_title('XANES Cross Section')
            self.plt.set_xlabel('Energies eV')
            self.plt.set_ylabel('Absorption Cross-section')
            
            #fontp=FontProperties()
            self.fontp.set_size('x-small')
            self.plt.legend(prop=self.fontp, loc=0)
            
            self.canvas.show() 
        
        else:
            tkMessageBox.showerror(title = "plot XMU", message = "Must select xmu.dat file")
            self.xmu_ent.delete(0, Tk.END)
        
    def view_structure(self):
        """
        A visualization of a selected structure
        """
        file_name=tkFileDialog.askopenfilename(**self.file_opt)
        if file_name == '' or file_name==():
            return
        self.xmu_ent.delete(0, END)
        self.xmu_ent.insert(0, file_name)
        
        xmu = self.xmu_ent.get()
        exe = 'python ' + matgenie_dir + ' view '
        
        subprocess.Popen(exe + xmu, shell= True, stdout = subprocess.PIPE)
        
#####################################################################

    def view_current_structure(self):
        """
        visualization of current structure
        """
        if cif_text.struc(cif) != '':
            vis = StructureVis()
            vis.set_structure(cif_text.struc(cif))
            vis.show()
        else:
            return

        
        
    def feff_ldos(self,option):
        """
        Plot feff LDOS density of states from ldos.dat files
        
        Args:
            option:
                specifies whether plot by -s(site), -e(element), -o(orbital)  
        """
        file_name=tkFileDialog.askopenfilename(**self.file_opt)
        if file_name == '' or file_name==():
            return
        self.xmu_ent.delete(0, END)
        self.xmu_ent.insert(0, file_name)
        file_type = file_name.split(".")[-1]
        if file_type == 'dat':
            directory = ''
            directory_list = file_name.split('/')
            for dir in directory_list[:-1]:
                directory = directory + '/' +dir
            directory = directory[1:]
            file_name=file_name[:-6]
                
            feffinpfile = directory + '/feff.inp'
            
            p = FeffLdos.from_file(feffinpfile, file_name)
            dos = p.complete_dos
            self.all_dos = OrderedDict()
            self.all_dos['Total'] = dos
            structure = p.complete_dos.structure
          
            if option == '-s':
                for i in xrange(len(structure)):
                    site = structure[i]
                    self.all_dos['Site ' + str(i) + " " + site.specie.symbol] = \
                      dos.get_site_dos(site)
            if option == '-e':
                self.all_dos.update(dos.get_element_dos())
            if option == '-o':
                self.all_dos.update(dos.get_spd_dos())
                
            #display
            keys = self.all_dos.keys()
            for label in keys:
                energies = self.all_dos[label].energies - self.all_dos[label].efermi
                densities =  self.all_dos[label].densities
                efermi = self.all_dos[label].efermi
                self._doses[label] = {'energies': energies, 'densities': densities,
                                      'efermi': efermi}
            
            y = None
            alldensities = []
            allenergies = []
            """
            Note that this complicated processing of energies is to allow for
            stacked plots in matplotlib.
            """
            for key, dos in self._doses.items():
                energies = dos['energies']
                densities = dos['densities']
                if not y:
                    y = {Spin.up: np.zeros(energies.shape),
                         Spin.down: np.zeros(energies.shape)}
                newdens = {}
                for spin in [Spin.up, Spin.down]:
                    if spin in densities:
                        if self.stack:
                            y[spin] += densities[spin]
                            newdens[spin] = y[spin].copy()
                        else:
                            newdens[spin] = densities[spin]
                allenergies.append(energies)
                alldensities.append(newdens)
    
            keys = list(self.all_dos.keys())
            keys.reverse()
            alldensities.reverse()
            allenergies.reverse()
            allpts = []
            for i, key in enumerate(keys):
                x = []
                y = []
                for spin in [Spin.up, Spin.down]:
                    if spin in alldensities[i]:
                        densities = list(int(spin) * alldensities[i][spin])
                        energies = list(allenergies[i])
                        if spin == Spin.down:
                            energies.reverse()
                            densities.reverse()
                        x.extend(energies)
                        y.extend(densities)
                allpts.extend(zip(x, y))
                if self.stack:
                    self.plt.fill(x, y, color=self.color_order[i % len(self.color_order)],
                             label=str(key))
                else:
                    self.plt.plot(x, y, color=self.color_order[i % len(self.color_order)],
                             label=str(key))
                if not self.zero_at_efermi:
                    ylim = self.plt.ylim()
                    self.plt.plot([self._doses[key]['efermi'],
                              self._doses[key]['efermi']], ylim,
                             self.color_order[i % 4] + '--', linewidth=2)
                    
                    
            self.plt.set_xlabel('Energies (eV)')
            self.plt.set_ylabel('Density of states')
            
            self.fontp.set_size('x-small')
            self.plt.legend(prop=self.fontp, loc=0)
            
            self.canvas.show()
                                   
        else:
            tkMessageBox.showerror(title = "feff_ldos by site", message = "Must select Ldos.dat file")
            self.xmu_ent.delete(0, Tk.END)
        
            
    def dos_plot(self, option):
        """
        Plot feff DOS density of states from vasprun.xml files
        
        Args:
            option:
                specifies whether plot by -s(site), -e(element), -o(orbital)  
        """
        file_name=tkFileDialog.askopenfilename(**self.file_opt)
        if file_name == '' or file_name==():
            return
        self.xmu_ent.delete(0, END)
        self.xmu_ent.insert(0, file_name)
        file_type = file_name.split(".")[-1]
        if file_type == 'xml':
             
            v = Vasprun(file_name)
            dos = v.complete_dos
        
            #all_dos = OrderedDict()
            self.all_dos["Total"] = dos
        
            structure = v.final_structure
            
            if option == '-s':
                for i in xrange(len(structure)):
                    site = structure[i]
                    self.all_dos["Site " + str(i) + " " + site.specie.symbol] = \
                        dos.get_site_dos(site)
                        
            if option == '-e':
                for el, dos in dos.get_element_dos().items():
                    self.all_dos[el] = dos
                
            if option == '-o':
                self.all_dos = dos.get_spd_dos()
            
            keys = self.all_dos.keys()
            for label in keys:
                energies = self.all_dos[label].energies - self.all_dos[label].efermi
                densities =  self.all_dos[label].densities
                efermi = self.all_dos[label].efermi
                self._doses[label] = {'energies': energies, 'densities': densities,
                                      'efermi': efermi}
            
            y = None
            alldensities = []
            allenergies = []
            """
            Note that this complicated processing of energies is to allow for
            stacked plots in matplotlib.
            """
            for key, dos in self._doses.items():
                energies = dos['energies']
                densities = dos['densities']
                if not y:
                    y = {Spin.up: np.zeros(energies.shape),
                         Spin.down: np.zeros(energies.shape)}
                newdens = {}
                for spin in [Spin.up, Spin.down]:
                    if spin in densities:
                        if self.stack:
                            y[spin] += densities[spin]
                            newdens[spin] = y[spin].copy()
                        else:
                            newdens[spin] = densities[spin]
                allenergies.append(energies)
                alldensities.append(newdens)
    
            keys = list(self.all_dos.keys())
            keys.reverse()
            alldensities.reverse()
            allenergies.reverse()
            allpts = []
            for i, key in enumerate(keys):
                x = []
                y = []
                for spin in [Spin.up, Spin.down]:
                    if spin in alldensities[i]:
                        densities = list(int(spin) * alldensities[i][spin])
                        energies = list(allenergies[i])
                        if spin == Spin.down:
                            energies.reverse()
                            densities.reverse()
                        x.extend(energies)
                        y.extend(densities)
                allpts.extend(zip(x, y))
                if self.stack:
                    self.plt.fill(x, y, color=self.color_order[i % len(self.color_order)],
                             label=str(key))
                else:
                    self.plt.plot(x, y, color=self.color_order[i % len(self.color_order)],
                             label=str(key))
                if not self.zero_at_efermi:
                    ylim = self.plt.ylim()
                    self.plt.plot([self._doses[key]['efermi'],
                              self._doses[key]['efermi']], ylim,
                             self.color_order[i % 4] + '--', linewidth=2)
                    
                    
            self.plt.set_xlabel('Energies (eV)')
            self.plt.set_ylabel('Density of states')
            
            self.fontp.set_size('x-small')
            self.plt.legend(prop=self.fontp, loc=0)
            
            self.canvas.show()
                                           
        else:
            tkMessageBox.showerror(title = "dos by site", message = "Must select vasprun.xml file")
            self.xmu_ent.delete(0, Tk.END)

    def plotchgint(self):
        """
        Plot charge integration from CHGCAR files  
        """
        file_name=tkFileDialog.askopenfilename(**self.file_opt)
        if file_name == '' or file_name==():
            return
        self.xmu_ent.delete(0, END)
        self.xmu_ent.insert(0, file_name)
        file_name2 = file_name.split("/")[-1]
        file_type = file_name2.split(".")[0]
        if file_type =='CHGCAR':
        
            chgcar = Chgcar.from_file(file_name)
            s = chgcar.structure
    
            finder = SymmetryFinder(s, symprec=0.1)
            sites = [sites[0] for sites in
                     finder.get_symmetrized_structure().equivalent_sites]
            atom_ind = [s.sites.index(site) for site in sites]
        
            for i in atom_ind:
                d = chgcar.get_integrated_diff(i, 3, 30) #radius default is 3
                self.plt.plot(d[:, 0], d[:,1],
                         label="Atom {} - {}".format(i, s[i].species_string))
            #self.plt.legend(loc="upper left")
            self.plt.set_xlabel("Radius (A)")
            self.plt.set_ylabel("Integrated charge (e)")
            
            self.fontp.set_size('x-small')
            self.plt.legend(prop=self.fontp, loc=0)
            
            self.canvas.show()
        
        else:
            tkMessageBox.showerror(title = "plot charge integration", message = "Must select CHGCAR file")
            self.xmu_ent.delete(0, Tk.END)
                
    def clear_graph(self):
        """
        Clears graph canvas
        """
        #clear text
        self.xmu_ent.delete(0, Tk.END)
        
        #clear graph
        self.plt.clear() # attributes from 'FigureCanvasTkAgg'
        self.canvas.draw() # attributes from 'FigureCanvasTkAgg'
        
        
    def _quit(self):
        """
        Exits or destroys GUI window
        """
        #exit
        root.quit()
        root.destroy()
        

        
#####################################################################################################################
 
class cif_text(Tk.Frame):
    """
    Creates a visual text structure of the basic functions of pymatgen 
    """
    
    
    def __init__(self, master):
        """
        Initialize constructor method will automatically invoked the GUI frames including buttons, menubar, labels and canvas
        
        Args:
            master:
                In Tkinter, master is a toplevel window manager and contains a given widgets
        """
        
        master.title('Graphical User Interface for Pymatgen')
        
        Tk.Frame.__init__(self, master, bd = 2)
        
        self.fstruc = ''
        

        #menu bar
        
        self.menubar = Menu(self)
        
        menu = Menu(self.menubar, tearoff = 0)
        self.menubar.add_cascade(label = 'File', menu = menu)
        menu.add_command(label = 'Open', command = self.open_file)
        menu.add_command(label = 'Save', command = self.save_file)
        menu.add_command(label = 'Save as', command = self.save_as_file)
        
        menu = Menu(self.menubar, tearoff = 0)
        self.menubar.add_cascade(label = 'Edit', menu = menu)
        menu.add_command(label = 'Cut', accelerator='Ctrl+x', command=lambda:
                        self.text.event_generate('<Control-x>'))
        menu.add_command(label = 'Copy', accelerator='Ctrl+c', command=lambda:
                        self.text.event_generate('<Control-c>'))
        menu.add_command(label = 'Paste', accelerator='Ctrl+v', command=lambda:
                        self.text.event_generate('<Control-v>'))
       
        menu = Menu(self.menubar, tearoff = 0)
        self.menubar.add_cascade(label = 'Material Genie', menu = menu)

        menu.add_command(label = 'Analyze VASP output directory tree', command = self.analyze_vasp)
        menu.add_command(label = 'Analyze VASP output directory tree for ion magnetization', command = self.get_magnetization)

        #menu.add_command(label = 'Create VASP input files from POSCAR, CSSR, or cif file', command = self.make_vasp_input)
        menu.add_command(label = 'Find Space Group, from POSCAR, CSSR, cif, or vasprun.xml', command = self.find_space_group) 
        
        menu = Menu(self.menubar, tearoff = 0)
        self.menubar.add_cascade(label = 'Help', menu = menu)
        
        menu.add_command(label = 'How to use GUI', command = self.help)
        menu.add_command(label = 'About', command = self.about)
        
        try:
            self.master.config(menu = self.menubar)
        except AttributeError:
            self.master.tk.call(master, 'config', '-menu', self.menubar)
        
        frame2 = Frame(root)
        frame2.pack(anchor = NW)
        
        b6 = Button(frame2, text = 'Find Material', command = self.find_material_button)
        b6.grid(row = 0, column = 0, sticky = Tk.W)
        
        self.mat_ent = Tk.Entry(frame2)
        self.mat_ent.bind('<Return>', self.find_material)
        self.mat_ent.grid(row = 0, column = 1, sticky = Tk.W)
        
        Tk.Label(frame2, text = 'Enter formula or element list, \n Ex: FE203 or Fe-0').grid(row = 0, column = 2, columnspan = 2, sticky = Tk.W)
        
        b6 = Button(frame2, text = 'Get Structure', command = self.get_structure_button)
        b6.grid(row = 1, column = 0, sticky = Tk.W)
        
        self.get_ent = Tk.Entry(frame2)
        self.get_ent.bind('<Return>', self.get_structure)
        self.get_ent.grid(row = 1, column = 1, sticky = Tk.W)
        
        
        Tk.Label(frame2, text = 'Enter \'Material ID\' to get structure').grid(row = 1, column = 2, columnspan = 2, sticky = Tk.W)
            
        # create instruction label
        frame1 = Frame(root)
        frame1.pack(anchor = NW)
        
        Tk.Label(frame1, text = 'Enter cif, poscar, or vasprun file').grid(row = 0, column = 0, columnspan = 2, sticky = Tk.W)

        # create a label and text entry
        Button(frame1, text = 'Browse', command = self.askopenfile_name).grid(row = 1, column = 0, sticky = Tk.W)
        
        self.cif_ent = Tk.Entry(frame1, width = 50) #frame1 instead of self
        self.cif_ent.grid(row = 1, column = 1, sticky = Tk.W)        

        #create a button
        
        frame = Frame(root) #row of buttons
        frame.pack(anchor = NW) #row of buttoms
        
        
        b2 = Button(frame, text = 'Create a feff.inp file', command = self.msg_box)
        b2.pack(side = LEFT)
        
        b5 = Button(frame, text = 'Display Structure', command = self.structure_display)
        b5.pack(side = LEFT)
        
        b3 = Button(frame, text = 'Clear text', command = self.clear_text)
        b3.pack(side = LEFT)
        
        b4 = Button(frame, text = 'Exit', command = self._quit)
        b4.pack(side = LEFT)
        
        self.file_opt = option = {}
        option['defaultextension'] = '.cif' or '.xml'
        option['filetypes'] = [('all files', '.*'), ('feff cif files', '*.cif'), ('vasprunfiles', '*.xml')]
        option['initialdir'] = '../test_files'
        option['initialfile'] = ''
        option['parent'] = root
        option['title'] = 'Select file'

	self.dir_opt = options = {}
	options['initialdir'] = '../test_files'
	options['mustexist'] = False
	option['parent'] = root
	option['title'] = 'Select Directory'
		
		
        # create a scroll bar and text box
        
        self.scroll_bar = Tk.Scrollbar(root)
        self.scroll_bar.pack(side = Tk.RIGHT, fill = Tk.Y)
        
        self.scroll_xbar = Tk.Scrollbar(root, orient = Tk.HORIZONTAL)
        self.scroll_xbar.pack(side = Tk.BOTTOM, fill = Tk.X)
        
        self.structure_text=Tk.Text(root)
        self.structure_text.pack(side = Tk.LEFT, fill = Tk.BOTH, expand = 1)
        
    def struc(self):
        """
        returns currently loaded structure
        """
        return self.fstruc
    
    def askopenfile_name(self):     
        """Returns an opened file in read mode.
        This time the dialog just returns a filename and the file is opened by your own code.
        """
        self.clear_text()
        
        #get filename
        file_name = tkFileDialog.askopenfilename(**self.file_opt)
        self.source = file_name
        if file_name == '' or file_name==():
            return
        self.cif_ent.insert(0, file_name)
        file_type = file_name.split(".")[-1]

        if file_type == 'cif':
            
            r = CifParser(self.source)
            self.fstruc = r.get_structures()[0]
            
        else:
            
            self.fstruc = read_structure(file_name)

    def msg_box(self): 
        """
        A message box for entering a symbol of absorbing atoms from create a feff.inp file
        """
        self.box=Toplevel()
        label0 = Label(self.box, text='Enter Symbol of absorbing Atom')
        label0.pack()

        self.box.entry0 = Entry(self.box)
        self.box.entry0.pack()

        var=IntVar()
        r1 = Radiobutton(self.box, text='XANES', variable=var, value=1).pack(anchor=W)
        r2 = Radiobutton(self.box, text='EXAFS', variable=var, value=2).pack(anchor=W)


        button1 = Button(self.box, text='Submit', command=lambda: self.submit_feff(var,self.box))
        button1.pack()

        button2 = Button(self.box, text='Cancel', command=lambda: self.box.destroy())
        button2.pack()
            

    def submit_feff(self,var,box):
        """
        Enter symbol of absorbing atoms to convert to feff.inp file
        
        Args:
            var:
                XANES or EXAFS option
            box:
                is the toplevel manager of the message box window
        """
        x = FeffInputSet("MaterialsProject")
        self.central_atom = box.entry0.get()

        is_central_atom=False
        for site in self.fstruc:
            if self.central_atom == site.specie.symbol:
                is_central_atom=True
        
        if is_central_atom:
            print 'var = ',var
            if var.get() == 1:
                self.calc_type = 'XANES'
            else:
                self.calc_type = 'EXAFS'

            if self.fstruc != '':
                structure = self.fstruc
                feff_dict = FeffInputSet.to_dict(x, structure,
                                                  self.calc_type,self.source,
                                                  self.central_atom,)
                self.feff_input = feff_dict['feff.inp']

        # display
#                self.structure_text.insert(Tk.END, '\n')
                self.clear_text()
                for line in self.feff_input:              
                    self.structure_text.insert(END, line)
                    
            else:
                self.structure_text.insert(1.0, '\nMust Generate a structure object from either cif_file or vasprun.xml file first')
        else:
            self.structure_text.insert(1.0,'\nCentral Atom Not Found in Structure, Choose Another')
        
        self.box.destroy()
        
            
    def find_material(self, event):
        """
        List materials from MP database using formula or elements
        """
        matproj=mp.MPRester("DIiNE4zmm8ATO0so")
        text=self.mat_ent.get()
        if text=='':
            self.structure_text.insert(1.0, '\nMust Enter Formula like Fe2O3 or Elements like Fe-O\n')
        else:
            entries=matproj.get_entries(text)
            for item in entries:
                text='\nMaterial ID:'+str(item.data['material_id'])+'  Formula: '+item.data['pretty_formula']
                text=text+'  Crystal System:  '+item.data['spacegroup']['crystal_system']
                text=text+'\n          Symmetry Number:'+str(item.data['spacegroup']['number'])
                text=text+'  Energy per Atom:'+str(item.data['energy_per_atom'])+'\n\n'
                self.structure_text.insert(1.0, text)  
                self.structure_text.config(yscrollcommand = self.scroll_bar.set)
                self.scroll_bar.config(command = self.structure_text.yview)
                
    def find_material_button(self):
        """
        List materials from MP database using formula or elements
        """
        matproj=mp.MPRester("DIiNE4zmm8ATO0so")
        text=self.mat_ent.get()
        if text=='':
            self.structure_text.insert(1.0, '\nMust Enter Formula like Fe2O3 or Elements like Fe-O\n')
        else:
            entries=matproj.get_entries(text)
            for item in entries:
                text='\nMaterial ID:'+str(item.data['material_id'])+'  Formula: '+item.data['pretty_formula']
                text=text+'  Crystal System:  '+item.data['spacegroup']['crystal_system']
                text=text+'\n          Symmetry Number:'+str(item.data['spacegroup']['number'])
                text=text+'  Energy per Atom:'+str(item.data['energy_per_atom'])+'\n\n'
                self.structure_text.insert(1.0, text)  
                self.structure_text.config(yscrollcommand = self.scroll_bar.set)
                self.scroll_bar.config(command = self.structure_text.yview)                
                
    def get_structure(self, event):
        """
        Gets material structure object using material ID from MP database
        """
        matproj=mp.MPRester("DIiNE4zmm8ATO0so")
        ID=self.get_ent.get()
        self.source = ID      
        if ID == '':
            self.structure_text.insert(1.0, '\nNo Structure ID Number Entered\n')
        else:
            self.fstruc=matproj.get_structure_by_material_id(str(ID))
            self.structure_text.insert(1.0, self.fstruc)
            self.structure_text.config(yscrollcommand = self.scroll_bar.set)
            self.scroll_bar.config(command = self.structure_text.yview)
            self.structure_text.insert(1.0, '\n\n')
        
        
    def get_structure_button(self):
        """
        Gets material structure object using material ID from MP database
        """
        matproj=mp.MPRester("DIiNE4zmm8ATO0so")
        ID=self.get_ent.get()
        self.source = ID      
        if ID == '':
            self.structure_text.insert(1.0, '\nNo Structure ID Number Entered\n')
        else:
            self.fstruc=matproj.get_structure_by_material_id(str(ID))
            self.structure_text.insert(1.0, self.fstruc)
            self.structure_text.config(yscrollcommand = self.scroll_bar.set)
            self.scroll_bar.config(command = self.structure_text.yview)
            self.structure_text.insert(1.0, '\n\n')        
           
    def structure_display(self):
        """
        Displays structure summary
        """
        
        self.structure_text.delete(1.0, Tk.END)
        
        if self.fstruc!= '':
            structure = self.fstruc
            self.structure_text.insert(Tk.END, structure)
            #add scroll bar to text    
            self.structure_text.config(yscrollcommand = self.scroll_bar.set)
            self.scroll_bar.config(command = self.structure_text.yview)
            
        else:
            
            self.structure_text.insert(Tk.END, 'Must Generate a structure object from cif_file')
            
    def analyze_vasp(self):
        """
        Extract computed properties from a VASP run tree using vasprun.xml files,
        use Browse button to locate top of VASP tree
        """
        
        vasp_root_dir= tkFileDialog.askdirectory()
        if vasp_root_dir=='' or vasp_root_dir == ():
            self.structure_text.insert(1.0, '\nSelect Directory')
        else:
            self.structure_text.insert(1.0,'\nRoot Directory\n'+vasp_root_dir+'\n')
            
            execute ='python ' + matgenie_dir + ' analyze '+vasp_root_dir+' -f -v -d -p -s energy_per_atom'
            text_out = subprocess.Popen([execute], shell=True, stdout=subprocess.PIPE).communicate()[0]            
            self.structure_text.insert(1.0, text_out+'\n')
            
            self.structure_text.config(yscrollcommand = self.scroll_bar.set)
            self.scroll_bar.config(command = self.structure_text.yview)
            self.structure_text.config( wrap = Tk.NONE, xscrollcommand = self.scroll_xbar.set)
            self.scroll_xbar.config(command = self.structure_text.xview)
        
    def get_magnetization(self):       
        """
        Extract computed properties for ion magnetization from a VASP run tree using vasprun.xml files,
        use Browse button to locate top of VASP tree
        """
        
        vasp_root_dir=tkFileDialog.askdirectory()
        if vasp_root_dir=='' or vasp_root_dir == ():
            self.structure_text.insert(1.0, '\nSelect Directory')
        else:
            self.structure_text.insert(1.0,'\nRoot Directory\n'+vasp_root_dir+'\n')
            execute='python ' + matgenie_dir + ' analyze '+vasp_root_dir+' -m 0-6'
            text_out = subprocess.Popen([execute], shell=True, stdout=subprocess.PIPE).communicate()[0]            
            self.structure_text.insert(1.0, text_out+'\n')
            
            self.structure_text.config(yscrollcommand = self.scroll_bar.set)
            self.scroll_bar.config(command = self.structure_text.yview)
            self.structure_text.config( wrap = Tk.NONE, xscrollcommand = self.scroll_xbar.set)
            self.scroll_xbar.config(command = self.structure_text.xview)

#    def make_vasp_input(self):
#        """generate a set of VASP input files"""
#        file_name=tkFileDialog.askopenfilename(**self.file_opt)
#        if file_name == '' or file_name==():
#            return
#        self.cif_ent.delete(0, END)
#        self.cif_ent.insert(0, file_name)
        
#        execute='python matgenie.py convert ' + file_name +' VASP_Input -o VASP'
#        subprocess.Popen([execute], shell=True)
#        self.structure_text.insert(END, 'VASP input has generated in ')    
            
    def find_space_group(self):
        """
        Find space group symmetry 
        """
        file_name=tkFileDialog.askopenfilename(**self.file_opt)
        if file_name == '' or file_name==():
            return
        self.cif_ent.delete(0, END)
        self.cif_ent.insert(0, '\n'+file_name)
        
        execute='python ' + matgenie_dir +'  symm ' + file_name +' -s'
        text_out = subprocess.Popen([execute], shell=True, stdout=subprocess.PIPE).communicate()[0]
        self.structure_text.insert(END, text_out+'\n')
            
    def help(self):
        """
        the help tab gives you a brief description on each functions on the GUI
        """
        
        
        description = "A graphical user interface that supports the basic functions of pymatgen, including.. \n \n \
        Menubar:\n \
            File:\n \
                open \n \
                save\n \
                save as \n \
            Edit:\n \
                cut \n \
                copy \n \
                paste \n \
            Material Genie: \n \
                Analyze VASP output directory tree- Extract computed properties from a VASP run tree using vasprun.xml files \n \
                Analyze VASP output directory tree for ion magnetization- Extract computed properties for ion magnetization from a VASP run tree using vasprun.xml files\n \
                Find Space Group, from POSCAR, CSSR, cif, or vasprun.xml- Find space group symmetry\n\n \
        buttons: \n \
            Plot: \n \
                Plot XMU.dat- Plot feff cross section \n \
                Plot LDOS from FEFF LDOS00.dat file:\n \
                    Site- Plot feff LDOS density of states by site\n \
                    Element- Plot feff LDOS density of states by element\n \
                    Orbital- Plot feff LDOS density of states by orbital\n \
                Plot DOS from vasprun.xml file:\n \
                    Site- Plot feff DOS density of states by site\n \
                    Element- Plot feff DOS density of states by element\n \
                    Orbital- Plot feff DOS density of states by orbital\n \
                Plot Charge integration-  Plot charge integration\n \
            View structure- visualization of selected structure\n \
            Clear graph- clear graph\n \
            Exit- destroy GUI window\n\n \
            Find Materials- List materials from MP database using formula or elements\n \
            Get Structure- Gets material structure object using material ID from MP database\n \
            Browse- From file dialog opens a filename\n \
            Create a feff.inp file:\n \
                message box: Enter symbol of absorbing atoms\n \
                    Radio button- XANES or EXAFS\n \
                    Submit- converts structure to feff.inp file\n \
                    Cancel- destroys message box\n \
            Display Structure- Displays structure summary\n \
            Clear text- Clear text\n \
            Exit- destroy GUI window"
        
        
        self.structure_text.insert(1.0,description)
        #add scroll bar to text    
        self.structure_text.config(yscrollcommand = self.scroll_bar.set)
        self.scroll_bar.config(command = self.structure_text.yview)
        self.structure_text.config( wrap = Tk.NONE, xscrollcommand = self.scroll_xbar.set)
        self.scroll_xbar.config(command = self.structure_text.xview)
        
    def about(self):
        """
        About tab gives detail about GUI.
        """
        
        detail = "A Graphical user interface that supports the basic functions of pymatgen.\n \n\
        \nAuthors: Megan LaRue \n\
	\nCredits: Alan Dozier, Shyue Ping Ong, Anubhav Jain \n\
        \nReference: \nShyue Ping Ong, William Davidson Richards, Anubhav Jain, Geoffroy Hautier,\
        \nMichael Kocher, Shreyas Cholia, Dan Gunter, Vincent Chevrier, Kristin A. Persson,\
        \nGerbrand Ceder. Python Materials Genomics (pymatgen) : A Robust,\
        \nOpen-Source Python Library for Materials Analysis.\
        \nComputational Materials Science, 2013, 68, 314319. doi:10.1016/j.commatsci.2012.10.028 \n\
        \nCopyright: Copyright 2011, The Materials Project \n\
        \nVersion: 1.2 \n\
        \nMaintainer: Megan LaRue \n\
        \nEmail: meganlarue79@gmail.com \n\
        \nStatus: Beta \n\
        \nDate: August 12, 2013 \n"
        
        self.structure_text.insert(1.0,detail)
        #add scroll bar to text    
        self.structure_text.config(yscrollcommand = self.scroll_bar.set)
        self.scroll_bar.config(command = self.structure_text.yview)
        self.structure_text.config( wrap = Tk.NONE, xscrollcommand = self.scroll_xbar.set)
        self.scroll_xbar.config(command = self.structure_text.xview)
        

    def clear_text(self):
        """
        Clears canvas text
        """
        self.get_ent.delete(0,Tk.END)
        self.mat_ent.delete(0, Tk.END)
        self.cif_ent.delete(0, Tk.END)
        self.structure_text.delete(1.0, Tk.END)
        
    def open_file(self):
        """
        General file opening to display in text box
        """
        file_name = tkFileDialog.askopenfilename()

        self.sfname=file_name

        with open(file_name,'r') as f:
            text_data=f.read()
        f.closed
        self.clear_text()
        self.structure_text.insert(END, text_data)
        self.structure_text.config(yscrollcommand = self.scroll_bar.set)
        self.scroll_bar.config(command = self.structure_text.yview)

    def save_as_file(self):
        """
        Names & saves file from the text canvas
        """

        text_data=self.structure_text.get(0.0, END)
        file_name=tkFileDialog.asksaveasfilename()
        f=open(file_name, 'w')
        f.write(text_data)
        f.close()

    def save_file(self):
        """
        Saves file from the text canvas
        """

        text_data=self.structure_text.get(0.0, END)

        if (text_data!='') and (self.sfname!=''):            
            f=open(self.sfname, 'w')
            f.write(text_data)
            f.close()

    def _quit(self):
        """
        Exits or destroys GUI window
        """

        root.quit()
        root.destroy()
        

#runs GUI and creates instances of classes

gra = Graph(root)

cif = cif_text(root)


Tk.mainloop()