package spiderdrawer.ui;

import java.awt.Dimension;
import java.awt.FileDialog;
import java.awt.GraphicsEnvironment;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.FilenameFilter;
import java.io.IOException;
import java.nio.ByteBuffer;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Paths;

import javax.imageio.ImageIO;
import javax.swing.JDialog;
import javax.swing.JMenu;
import javax.swing.JMenuBar;
import javax.swing.JMenuItem;
import javax.swing.JOptionPane;

/**
 *
 * @author charliebashford
 */
public class MainForm extends JDialog {
	
	private DrawingPanel drawingPanel;
    final JMenuItem undoMenuItem = new JMenuItem();
    final JMenuItem redoMenuItem = new JMenuItem();
    boolean done = false;
    boolean originalRep;
    int majorVersion = 0;
    int minorVersion = 1;
    int revisionVersion = 2;
	
    /**
     * Creates new form MainForm
     */
    public MainForm(java.awt.Frame parent, boolean modal, boolean originalRep) {
    	super(parent, modal);
    	this.originalRep = originalRep;
        initComponents();
    }
    
    private void clearMenuItemClicked() {
    	drawingPanel.clearDrawable();
    	drawingPanel.repaint();
    }
    
    private void convertMenuItemClicked() {
    	String textRep = getSpiderDiagram();
    	if (isModal() && textRep != null) {
    		done = true;
    		setVisible(false);
    	}
    }
    
    public String getSpiderDiagram() {
    	String textRep = drawingPanel.textualRep(originalRep);
    	System.out.println(textRep);
    	return textRep;
    }
    
    private void loadMenuItemClicked() {
    	String filename = FileChooserForm.showDialog(this, new File(".").getAbsolutePath());
    	if (filename == null || filename.equals("")) {
    		return;
    	}
		String content = null;
		try {
			byte[] encoded = Files.readAllBytes(Paths.get(filename + ".spi"));
	    	content = Charset.defaultCharset().decode(ByteBuffer.wrap(encoded)).toString();
		} catch (IOException e) {
			e.printStackTrace();
		}
		drawingPanel.loadDrawablesString(content);
		drawingPanel.repaint();
    }
    
    private void saveMenuItemClicked() {
    	String name;
    	int result = JOptionPane.NO_OPTION;
    	File file;
    	do {
			do {
		    	name = JOptionPane.showInputDialog(this, "Enter name:", "Save", JOptionPane.PLAIN_MESSAGE);
		    	if (name == null) {
		    		return;
		    	}
			} while (name.equals(""));
			file = new File(name + ".spi");
			if(file.exists() && !file.isDirectory()) {
				result = JOptionPane.showConfirmDialog(null, "The file already exists! Want to choose a new name?", "Save", JOptionPane.YES_NO_CANCEL_OPTION, JOptionPane.PLAIN_MESSAGE);
				if (result == JOptionPane.CANCEL_OPTION) {
					return;
				}
			}
    	} while (result == JOptionPane.YES_OPTION);
    	try {	
			
			FileWriter fw = new FileWriter(file.getAbsoluteFile());
			BufferedWriter bw = new BufferedWriter(fw);
			bw.write(drawingPanel.drawablesAsString());
			bw.close();
    	} catch (IOException x) {
    	    System.err.format("IOException: %s%n", x);
    	}
    }
    
    private void exportMenuItemClicked() {
    	FileDialog fileDialog = new FileDialog(this, "Save", FileDialog.SAVE);
        fileDialog.setFilenameFilter(new FilenameFilter() {
            public boolean accept(File dir, String name) {
                return name.endsWith(".png");
            }
        });
        fileDialog.setFile("output.png");
        fileDialog.setVisible(true);
        String fileName = fileDialog.getFile();
    	if (fileName != null) {
    		File outputFile;
    		if (fileName.lastIndexOf('.') != -1 && fileName.substring(fileName.lastIndexOf('.') + 1).equals("png")) {
    			outputFile = new File(fileDialog.getDirectory() + fileDialog.getFile());
    		} else {
    			outputFile = new File(fileDialog.getDirectory() + fileDialog.getFile() + ".png");
    		}
    		try {
    			ImageIO.write(drawingPanel.createImage(), "png", outputFile);
    		} catch (IOException e) {
    			JOptionPane.showMessageDialog(null, "Error exporting file.");
    		} 
    		//log.append("Saving: " + file.getName() + ".");
    	} else {
    		//log.append("Saving command cancelled by user.");
    	}	
    }
    
    private void initComponents() {
        //setSize(900, 650);
        setBounds(GraphicsEnvironment.getLocalGraphicsEnvironment().getMaximumWindowBounds()); 
        setLocationRelativeTo(null);
        setDefaultCloseOperation(javax.swing.WindowConstants.DISPOSE_ON_CLOSE);

        addDrawingFrame();
        addMenu();      
        
        /*messageBox = new MessageBox("Hello");
    	add(messageBox);*/
    }
    
    private void addDrawingFrame() {
    	drawingPanel = new DrawingPanel(this);
        this.setContentPane(drawingPanel);
    }
    
    private void addMenu() {
    	JMenuBar menuBar = new JMenuBar();
    	setJMenuBar(menuBar);
    	
        JMenu optionsMenu = new JMenu();
        optionsMenu.setText("Options");        
        menuBar.add(optionsMenu);
        
        JMenuItem aboutMenuItem = new JMenuItem();
        aboutMenuItem.setText("About");
        aboutMenuItem.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent e) {
				JOptionPane.showMessageDialog(null, "Version: " + majorVersion + "." + minorVersion + ((revisionVersion != 0) ? "." + revisionVersion : ""), "About", JOptionPane.INFORMATION_MESSAGE);		
			}
        });
        optionsMenu.add(aboutMenuItem);
        
        JMenuItem loadMenuItem = new JMenuItem();
        loadMenuItem.setText("Load");
        loadMenuItem.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent e) {
				loadMenuItemClicked();		
			}
        });
        optionsMenu.add(loadMenuItem);
        
        JMenuItem saveMenuItem = new JMenuItem();
        saveMenuItem.setText("Save");
        saveMenuItem.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent e) {
				saveMenuItemClicked();
			}
        });
        optionsMenu.add(saveMenuItem);
        
        JMenuItem exportMenuItem = new JMenuItem();
        exportMenuItem.setText("Export");
        exportMenuItem.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent e) {
				exportMenuItemClicked();				
			}
        });
        optionsMenu.add(exportMenuItem);
        
        JMenuItem clearMenuItem = new JMenuItem();
        clearMenuItem.setText("Clear");
        clearMenuItem.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent e) {
				clearMenuItemClicked();				
			}
        });
        optionsMenu.add(clearMenuItem);
        
        
        /*Test menu starts */
        JMenu testMenu = new JMenu();
        testMenu.setText("Test");
        //menuBar.add(testMenu);
        
        JMenuItem circleMenuItem = new JMenuItem();
        circleMenuItem.setText("Circle");
        circleMenuItem.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent e) {
				drawingPanel.addCircle();				
			}
        });
        testMenu.add(circleMenuItem);
        
        JMenuItem lineMenuItem = new JMenuItem();
        lineMenuItem.setText("Line");
        lineMenuItem.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent e) {
				drawingPanel.addLine();					
			}
        });
        testMenu.add(lineMenuItem);
        
        JMenuItem pointMenuItem = new JMenuItem();
        pointMenuItem.setText("Point");
        pointMenuItem.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent e) {
				drawingPanel.addPoint();					
			}
        });
        testMenu.add(pointMenuItem);
        
        JMenuItem labelMenuItem = new JMenuItem();
        labelMenuItem.setText("Label");
        labelMenuItem.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent e) {
				drawingPanel.addLabel();					
			}
        });
        testMenu.add(labelMenuItem);
        
        JMenuItem boxMenuItem = new JMenuItem();
        boxMenuItem.setText("Box");
        boxMenuItem.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent e) {
				drawingPanel.addBox();					
			}
        });
        testMenu.add(boxMenuItem);
        
        JMenuItem connectiveMenuItem = new JMenuItem();
        connectiveMenuItem.setText("Connective");
        connectiveMenuItem.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent e) {
				drawingPanel.addConnective();					
			}
        });
        testMenu.add(connectiveMenuItem);
        
        
        undoMenuItem.setText("Undo");
        undoMenuItem.setMinimumSize(new Dimension(60,0));
        undoMenuItem.setPreferredSize(new Dimension(60,0));
        undoMenuItem.setMaximumSize(new Dimension(60, Short.MAX_VALUE));
        undoMenuItem.setEnabled(false);
        undoMenuItem.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent e) {
				drawingPanel.undo();
				checkUndoRedo();
			}
        });
        menuBar.add(undoMenuItem);
        
        redoMenuItem.setText("Redo");
        redoMenuItem.setMinimumSize(new Dimension(60,0));
        redoMenuItem.setPreferredSize(new Dimension(60,0));
        redoMenuItem.setMaximumSize(new Dimension(60, Short.MAX_VALUE));
        redoMenuItem.setEnabled(false);
        redoMenuItem.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent e) {
				drawingPanel.redo();
				checkUndoRedo();
			}
        });
        menuBar.add(redoMenuItem);
        
        /* Convert Menu starts */
        
        JMenuItem convertMenuItem = new JMenuItem();
        convertMenuItem.setMinimumSize(new Dimension(80,0));
        convertMenuItem.setPreferredSize(new Dimension(80,0));
        convertMenuItem.setMaximumSize(new Dimension(80, Short.MAX_VALUE));
        convertMenuItem.setText("Done");
        convertMenuItem.addActionListener(new ActionListener(){
        	public void actionPerformed(ActionEvent e) {
				convertMenuItemClicked();	
			}
        });
        menuBar.add(convertMenuItem);

    }
    
    public void checkUndoRedo() {
    	undoMenuItem.setEnabled(drawingPanel.canUndo());
		redoMenuItem.setEnabled(drawingPanel.canRedo());
    }
    
    public boolean showDialog() {
    	done = false;
    	setVisible(true);
    	return done;
    }	
    
    /**
     * @param args the command line arguments
     */
    public static void main(String args[]) {
    	boolean originalRep = false;
    	if (args.length > 0)
    		originalRep = true;
    	System.out.println("Using original rep: " + originalRep);
        new MainForm(null, false, originalRep).setVisible(true);
    }


}
