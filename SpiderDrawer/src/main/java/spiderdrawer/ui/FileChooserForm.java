package spiderdrawer.ui;

import java.awt.BorderLayout;
import java.awt.Dimension;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.io.File;
import java.io.FilenameFilter;

import javax.swing.BorderFactory;
import javax.swing.Box;
import javax.swing.BoxLayout;
import javax.swing.DefaultListModel;
import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JLabel;
import javax.swing.JList;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.ListSelectionModel;


public class FileChooserForm extends JDialog implements ActionListener {

	private String directory;
	private String filename;
	private JList<String> list;
	
	public FileChooserForm(java.awt.Dialog parent, boolean modal, String directory) {
        super(parent, modal);
		this.directory = directory;
		initComponents();
   	}
	
    private void initComponents() {
        setSize(250, 650);
        setResizable(false);
        setLocationRelativeTo(null);
        setDefaultCloseOperation(javax.swing.WindowConstants.DISPOSE_ON_CLOSE);     
        getContentPane().setLayout(new BorderLayout());
        JButton cancelButton = new JButton("Cancel");
        cancelButton.addActionListener(this);
        
        JButton deleteButton = new JButton("Delete");
        deleteButton.setActionCommand("Delete");
        deleteButton.addActionListener(this);
        //
        final JButton loadButton = new JButton("Load");
        loadButton.setActionCommand("Load");
        loadButton.addActionListener(this);
        getRootPane().setDefaultButton(loadButton);
        
      //Lay out the buttons from left to right.
        JPanel buttonPane = new JPanel();
        buttonPane.setLayout(new BoxLayout(buttonPane, BoxLayout.LINE_AXIS));
        buttonPane.setBorder(BorderFactory.createEmptyBorder(0, 10, 10, 10));
        buttonPane.add(Box.createRigidArea(new Dimension(0,5)));
        buttonPane.add(cancelButton);
        buttonPane.add(Box.createHorizontalGlue());
        buttonPane.add(Box.createRigidArea(new Dimension(5, 0)));
        buttonPane.add(deleteButton);
        buttonPane.add(Box.createHorizontalGlue());
        buttonPane.add(Box.createRigidArea(new Dimension(5, 0)));
        buttonPane.add(loadButton);
        buttonPane.add(Box.createRigidArea(new Dimension(0,5)));
        
        String[] filenames = getFileNames();
        DefaultListModel<String> listModel = new DefaultListModel<>();
        for (int i = 0; i < filenames.length; i++) {
        	listModel.addElement(filenames[i]);
        }
        list = new JList<>(listModel);
        list.setLayoutOrientation(JList.VERTICAL);
        list.setVisibleRowCount(Math.max(5,  Math.min(15, list.getModel().getSize())));
    	list.addMouseListener(new MouseAdapter() {
            public void mouseClicked(MouseEvent e) {
                if (e.getClickCount() == 2) {
                    loadButton.doClick(); //emulate button click
                }
            }
        });
    	list.setSelectionMode(ListSelectionModel.SINGLE_INTERVAL_SELECTION);
        
        JScrollPane listScroller = new JScrollPane(list);
        listScroller.setAlignmentX(LEFT_ALIGNMENT);
        
        JPanel listPane = new JPanel();
        listPane.setLayout(new BoxLayout(listPane, BoxLayout.Y_AXIS));
        listPane.add(Box.createRigidArea(new Dimension(0,5)));
        listPane.add(listScroller);
        listPane.setBorder(BorderFactory.createEmptyBorder(10,10,10,10));
    	
        getContentPane().add(listScroller, BorderLayout.CENTER);
        getContentPane().add(buttonPane, BorderLayout.PAGE_END);
    }
    
    public void actionPerformed(ActionEvent e) {
        if (e.getActionCommand().equals("Load")) {
           filename = (String)(list.getSelectedValue());
        } else if (e.getActionCommand().equals("Delete")) {
        	filename = (String)(list.getSelectedValue());
        	if (filename != null && !filename.equals("")) {
        		File file = new File(filename + ".spi");
        		if(!file.delete()) {
        			System.out.println("Delete operation is failed.");
        			return;
        		}
        		int index = list.getSelectedIndex();
        		if(index >= 0){ //Remove only if a particular item is selected
        			DefaultListModel<String> model = (DefaultListModel<String>)list.getModel();
        			model.remove(index);
        		}
        	}
        	return;
        }
        this.setVisible(false);
    }
    
    private String[] getFileNames() {
    	File dir = new File(directory);

    	File[] files = dir.listFiles(new FilenameFilter() { 
    	         		public boolean accept(File dir, String filename)
    	         			{ return filename.endsWith(".spi"); }
    					} );
    	if (files == null) {
    		return null;
    	}
    	setSize(200, 30*(files.length)+40);
    	add(Box.createRigidArea(new Dimension(5,20)));
    	String[] filenames = new String[files.length];
    	for (int i = 0; i < files.length; i++) {
    		filenames[i] = files[i].getName().substring(0, files[i].getName().length()-4);
    	}
    	
    	return filenames;
    }
    
    public static String showDialog(java.awt.Dialog parent, String directory) {
    	FileChooserForm fileChooserForm = new FileChooserForm(parent, true, directory);
    	if (fileChooserForm.list.getModel().getSize() == 0) {
    		JOptionPane optionPane = new JOptionPane(new JLabel("No files to load!",JLabel.CENTER));  
    	    JDialog dialog = optionPane.createDialog("");  
    	    dialog.setModal(true);  
    	    dialog.setVisible(true);
    		return null;
    	}
    	fileChooserForm.pack();
    	fileChooserForm.setVisible(true);
    	return fileChooserForm.filename;
    }
    
    public static void main(String[] args) {
    	FileChooserForm.showDialog(null, new File(".").getAbsolutePath());
    }
	
}
