package spiderdrawer.ui;

import java.awt.BasicStroke;
import java.awt.Color;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.Rectangle;
import java.awt.RenderingHints;
import java.awt.event.ComponentAdapter;
import java.awt.event.ComponentEvent;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.awt.image.BufferedImage;

import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.SwingUtilities;

import spiderdrawer.Action;
import spiderdrawer.ActionManager;
import spiderdrawer.exception.EmptyContainerException;
import spiderdrawer.exception.InvalidShapeException;
import spiderdrawer.recognizer.RataRecognizer;
import spiderdrawer.recognizer.SpiderRecognizer;
import spiderdrawer.recognizer.TessRecognizer;
import spiderdrawer.shape.Arrays;
import spiderdrawer.shape.Box;
import spiderdrawer.shape.Circle;
import spiderdrawer.shape.Connective;
import spiderdrawer.shape.Freeform;
import spiderdrawer.shape.Label;
import spiderdrawer.shape.Line;
import spiderdrawer.shape.Logical;
import spiderdrawer.shape.Point;
import spiderdrawer.shape.Shading;
import spiderdrawer.shape.interfaces.Deletable;
import spiderdrawer.shape.interfaces.Drawable;
import spiderdrawer.shape.interfaces.Movable;
import spiderdrawer.shape.interfaces.Shape;
import static spiderdrawer.Parameters.RECOGNITION_SLEEP;

import java.lang.reflect.Constructor;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Random;
import java.util.Set;

/**
 *
 * @author charliebashford
 */
public class DrawingPanel extends JPanel {
    
    private final ArrayList<Shape> shapeList = new ArrayList<Shape>();
    private Freeform currentFreeform;
    private SpiderRecognizer spiderRecognizer;
    private RataRecognizer rataRecognizer;
    private Movable toMove;
    private Point from = null;
    private Point originalFrom = null;
    private Box drawingBox;
    private Action currentAction;
    private boolean deleted = false;
    private ActionManager actionManager = new ActionManager();
    private final MainForm mainForm;
    
    
    /**
     * Creates new form DrawFrame
     */
    public DrawingPanel(final MainForm mainForm) {
    	this.mainForm = mainForm;
        initComponents();
        spiderRecognizer = new SpiderRecognizer(shapeList);
        rataRecognizer = new RataRecognizer("/lib/spider.model");
        drawingBox = Box.create(0, 0, getWidth()-1, getHeight()-1, shapeList);
        shapeList.add(drawingBox);
        addComponentListener(new ComponentAdapter() {

            @Override
            public void componentResized(ComponentEvent e) {
               drawingBox.resize(getWidth()-1, getHeight()-1);
               drawingBox.recompute(false);
               repaint();
            }

         });
        addMouseListener(new MouseAdapter() {
            public void mousePressed(MouseEvent e) {
            	currentAction = new Action(shapeList);
	        	from = new Point(e.getX(), e.getY());
	        	originalFrom = from;
	        	deleted = false;
            	if (SwingUtilities.isRightMouseButton(e)) {
            		System.out.println("Mouse Down: Right clicking...");
            		currentAction.setDelete();
            		return;
            	}
	        	double minDist = Double.MAX_VALUE;
	        	for (int i = 0; i < shapeList.size(); i++) {
	        		if (shapeList.get(i) instanceof Movable) {
	        			Movable movable = (Movable) shapeList.get(i);
	        			if (movable.equals(drawingBox)) {
	        				continue;
	        			}
	        			double dist = movable.boundaryDistance(from);
	        			if (movable.isWithin(from) && dist < minDist) {
	        				toMove = movable;
	        				minDist = dist;
	        			}
	        		}
	        	}
	        	if (toMove != null) {
	        		return;
	        	}
	        	currentFreeform = new Freeform(e.getX(), e.getY());
	        	shapeList.add(currentFreeform);
            	repaint();
            }
            
            public void mouseReleased(MouseEvent e) {
            	try {
            	if (SwingUtilities.isRightMouseButton(e)) {
            		if (from == null)
            			return;
            		Line line = new Line(from, new Point(e.getX(), e.getY()));
            		for (int i = 0; i < shapeList.size(); i++) {
            			if (shapeList.get(i) instanceof Deletable) {
            				Deletable delShape = (Deletable) shapeList.get(i);
            				if (delShape.equals(drawingBox)) {
    	        				continue;
    	        			}
	            			if (delShape.intersects(line)  && !(delShape instanceof Shading)) {
	            				shapeList.remove(i);
	            				delShape.remove();
	            				currentAction.add(delShape);
	            			}
            			}
            		}
            		if (deleted == false) {
	            		for (int i = 0; i < shapeList.size(); i++) {
	            			if (shapeList.get(i) instanceof Shading) {
	            				Shading shading = (Shading) shapeList.get(i);
	            				if (shading.intersects(line)) {
		            				shapeList.remove(i);
		            				shading.remove();
		            				currentAction.add(shading);
	            				}
	            			}
	            		}
            		}
                	actionManager.add(currentAction);
            		repaint();
            	} else {
	            	if (toMove != null) {
	            		toMove.move(from, new Point(e.getX(), e.getY()));
	            		toMove.recompute(false);
	            		currentAction.setMove(toMove, originalFrom, new Point(e.getX(), e.getY()));
                    	actionManager.add(currentAction);
	            		toMove = null;
	            		from = null;
	            		repaint();
	            		return;
	            	}
		        	Thread timeThread = new Thread() {
		                public void run() {
		            		Freeform initial = currentFreeform;
		                    Shape shape = null;
		            		Freeform[] arrFreeform = {initial};
		            		if (initial.getOverlappingFreeforms(Arrays.freeformList(shapeList)).size() == 0 && !SpiderRecognizer.isTextSize(arrFreeform)) {
			            		String resultingClass = rataRecognizer.classify(initial);
		                    	System.out.println("Result:" + resultingClass);
		                    	switch(resultingClass) {
		                    		case "Text": shape = null; break;
		                    		case "Box": shape = Box.create(initial, shapeList); break;
		                    		case "Line":  shape = spiderRecognizer.checkLine(initial); break;
		                    		case "Circle": shape = Circle.create(initial, shapeList); break;
		                    		case "Dot": shape = Point.create(initial, shapeList); break;
		                    		case "Shading": shape = Shading.create(initial, shapeList); break;
		                    		case "Connective": shape = null; break;
		                    	}
		                    	if (shape != null)
			                    	shapeList.remove(initial);

		            		}
		            		if (shape == null) {
			                    try {
			                        Thread.sleep(RECOGNITION_SLEEP);
			                    } catch (InterruptedException e) {
			                        e.printStackTrace();
			                    }
			                    if (initial.isRemoved())
			                    	return;
			                    ArrayList<Freeform> overlapFreeforms = initial.getOverlappingFreeforms(Arrays.freeformList(shapeList));
		                    	overlapFreeforms.add(initial);
			                    boolean textSize = SpiderRecognizer.isTextSize(overlapFreeforms.toArray(new Freeform[0]));
			                    System.out.println(initial + ": textSize:" + textSize + " num " + overlapFreeforms.size() + " isLast" + initial.isLast(overlapFreeforms.toArray(new Freeform[0])));
			                    if (initial != null && (initial.equals(currentFreeform) || !textSize || initial.isLast(overlapFreeforms.toArray(new Freeform[0])))) {
			                    	if (overlapFreeforms.size() != 1 && !SpiderRecognizer.isAnyDotSize(overlapFreeforms.toArray(new Freeform[0]))) {
			                    		shape = spiderRecognizer.checkText(initial, true, true);
			                    	} else {
				                    	String resultingClass = rataRecognizer.classify(initial);
				                    	System.out.println("Result:" + resultingClass);
				                    	switch(resultingClass) {
				                    		case "Text": shape = spiderRecognizer.checkText(initial, false, true); break;
				                    		case "Box": shape = Box.create(initial, shapeList); break;
				                    		case "Line":  shape = spiderRecognizer.checkLine(initial); break;
				                    		case "Circle": shape = Circle.create(initial, shapeList); break;
				                    		case "Dot": shape = Point.create(initial, shapeList); break;
				                    		case "Shading": shape = spiderRecognizer.checkShading(initial); break;
				                    		case "Connective": shape = spiderRecognizer.checkText(initial, true, false); break;
				                    	}
				                    	if ((shape != null && !resultingClass.equals("Text")) || resultingClass.equals("Shading"))
				                    		shapeList.remove(initial);
			                    	}
			                    }
		            		}
		                    if (shape != null) {
		                    	if (!initial.isRemoved())
		                    		 shapeList.add(shape);
		                    	Action action = new Action(shapeList);
		                    	action.setCreate(shape);
		                    	actionManager.add(action);
		                    }
		                    repaint();
		                    mainForm.checkUndoRedo();
		                }
		            };
		
		            timeThread.setDaemon(true);
		            timeThread.start();
		            
            	}
            	mainForm.checkUndoRedo();
            	} catch (Exception ex) {
            		ex.printStackTrace();
            	}
            }
        });
        
        addMouseMotionListener(new MouseAdapter() {
            public void mouseDragged(MouseEvent e) {
            	if (SwingUtilities.isRightMouseButton(e)) {
            		if (!currentAction.isDelete())
            			currentAction.setDelete();
            		if (from == null)
            			return;
            		Point to = new Point(e.getX(), e.getY());
            		Line line = new Line(from, to);
            		for (int i = 0; i < shapeList.size(); i++) {
            			if (shapeList.get(i) instanceof Deletable) {
            				Deletable delShape = (Deletable) shapeList.get(i);
            				if (delShape.equals(drawingBox)) {
    	        				continue;
    	        			}
	            			if (delShape.intersects(line) && !(delShape instanceof Shading)) {
	            				shapeList.remove(i);
	            				delShape.remove();
	            				currentAction.add(delShape);
	            				deleted = true;
	            			}
            			}
            		}
            		from = to;
            	} else {
	            	if (toMove != null) {
	            		Point to = new Point(e.getX(), e.getY());
	            		toMove.move(from, to);
	            		toMove.recompute(true);
	            		from = to;
	            	} else {
	            		currentFreeform.addPoint(e.getX(), e.getY());
	            	}
            	}
                repaint();
            }
        });
    }
    
    public void addCircle() {
    	Random generator = new Random();
    	int x = generator.nextInt(getWidth());
    	int y = generator.nextInt(getHeight());
    	int radius = 30;
    	shapeList.add(Circle.create(x, y, radius, shapeList));
    	repaint();
    }
    
    public void addLine() {
    	Random generator = new Random();
    	int startX = generator.nextInt(getWidth());
    	int startY = generator.nextInt(getHeight());
    	int endX = generator.nextInt(getWidth());
    	int endY = generator.nextInt(getHeight());
    	shapeList.add(Line.create(startX, startY, endX, endY, shapeList));
    	repaint();
    }
    
    public void addPoint() {
    	Random generator = new Random();
    	int x = generator.nextInt(getWidth());
    	int y = generator.nextInt(getHeight());
    	shapeList.add(Point.create(x, y, shapeList));
    	repaint();
    }
    
    public void addLabel() {
    	Random generator = new Random();
    	int x = generator.nextInt(getWidth());
    	int y = generator.nextInt(getHeight());
    	int letterNumber = generator.nextInt(26);
    	char letter = (char) ('A' + letterNumber);
    	shapeList.add(Label.create(letter, new Point(x, y), shapeList));
    	repaint();
    }
    
    public void addLabel(char letter) {
    	Random generator = new Random();
    	int x = generator.nextInt(getWidth());
    	int y = generator.nextInt(getHeight());
    	shapeList.add(Label.create(letter, new Point(x, y), shapeList));
    	repaint();
    }
    
    public void addBox() {
    	Random generator = new Random();
    	int x = generator.nextInt(getWidth());
    	int y = generator.nextInt(getHeight());
    	int height = 50 + generator.nextInt(51);
    	int width = 50 + generator.nextInt(51);
    	shapeList.add(Box.create(x, y, width, height, shapeList));
    	repaint();
    }
    
    public void addConnective() {
    	Random generator = new Random();
    	int x = generator.nextInt(getWidth());
    	int y = generator.nextInt(getHeight());
    	int type = generator.nextInt(5);
    	shapeList.add(Connective.create(Logical.create(type), x, y, shapeList));
    	repaint();
    }
    
    public void clearDrawable() {
    	shapeList.clear();
    	actionManager = new ActionManager();
    	mainForm.checkUndoRedo();
    	drawingBox = Box.create(0, 0, getWidth()-1, getHeight()-1, shapeList);
    	shapeList.add(drawingBox);
    }
    
    public void undo() {
    	actionManager.undo();
    	repaint();
    }
    
    public void redo() {
    	actionManager.redo();
    	repaint();
    }
    
    public boolean canUndo() {
    	return actionManager.canUndo();
    }
    
    public boolean canRedo() {
    	return actionManager.canRedo();
    }
    
    public String drawablesAsString() {
    	StringBuilder sb = new StringBuilder();
    	for (int i = 0; i < shapeList.size(); i++) {
    		sb.append(shapeList.get(i).getClass().getName() + "\n");
    		if (shapeList.get(i) instanceof Freeform) {
    			sb.append(((Freeform) shapeList.get(i)).pointsAsString());
    		} else if (shapeList.get(i) instanceof Label) {
    			sb.append(((Label) shapeList.get(i)).asString());
    		} else if (shapeList.get(i) instanceof Circle) {
    			sb.append(((Circle) shapeList.get(i)).asString());
    		} 
    		if (i != shapeList.size() - 1) {
    			sb.append('\n');
    		}
    	}
    	return sb.toString();
    }

    
    @SuppressWarnings({ "rawtypes", "unchecked" })
	public boolean loadDrawablesString(String str) {
    	shapeList.clear();
    	if (str == null) {
    		return false;
    	}
    	String[] line = str.split("\n");
    	if (line.length == 0 || line.length % 2 == 1)
    		return false;
    	for (int i = 0; i < line.length; i += 2) {	
    		String[] parameters = line[i+1].split(",");
			try {
				Class newDrawableClass = Class.forName(line[i]);
				
				if (line[i].equals(Freeform.class.getCanonicalName())) {
					Class[] types = {ArrayList.class};
					ArrayList<Point> points = new ArrayList<Point>();
					for (int j = 0; j < parameters.length; j += 2) {
						points.add(new Point(Integer.parseInt(parameters[j]), Integer.parseInt(parameters[j+1])));
					}
					Constructor constructor = newDrawableClass.getConstructor(types);
	    			Object[] params = {points};
	    			shapeList.add((Drawable)constructor.newInstance(params));
				} else if (line[i].equals(Label.class.getCanonicalName())) {
					Class[] types = {Character.TYPE, Integer.TYPE, Integer.TYPE};
	    			Constructor constructor = newDrawableClass.getConstructor(types);
	    			Object[] params = {parameters[0].charAt(0), Integer.parseInt(parameters[1]), Integer.parseInt(parameters[2])};
	    			shapeList.add((Drawable)constructor.newInstance(params));
				} else if (line[i].equals(Circle.class.getCanonicalName())) {
					Class[] types = {Integer.TYPE, Integer.TYPE, Integer.TYPE};
	    			Constructor constructor = newDrawableClass.getConstructor(types);
	    			Object[] params = {Integer.parseInt(parameters[0]), Integer.parseInt(parameters[1]), Integer.parseInt(parameters[2])};
	    			shapeList.add((Drawable)constructor.newInstance(params));
				}
			} catch (Exception e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
				return false;
			}

    	}
    	return true;
    }
    
    
   
    
    @Override
    public void paintComponent(Graphics g) {
        super.paintComponent(g);
        Graphics2D g2 = (Graphics2D) g;
        g2.setStroke(new BasicStroke(2));
        g2.setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON);
        for (int i = 0; i < shapeList.size(); i++) {
        	if (shapeList.get(i) instanceof Circle) {
        		Circle circle = (Circle) shapeList.get(i);
        		circle.draw(g2);
        	}
        }
        for (int i = 0; i < shapeList.size(); i++) {
        	if (shapeList.get(i) instanceof Line) {
        		Line line = (Line) shapeList.get(i);
        		line.draw(g2);
        	}
        }
        for (int i = 0; i < shapeList.size(); i++) {
        	if (shapeList.get(i) instanceof Drawable && !(shapeList.get(i) instanceof Circle) && !(shapeList.get(i) instanceof Line)) {
        		Drawable drawable = (Drawable) shapeList.get(i);
        		if (drawable.equals(drawingBox)) {	
        			if (drawingBox.isValid())
        			continue;
        		}
        		drawable.draw(g2);
        	}
        }
    }
    
    public String textualRep(boolean originalRep) {
    	try {
    		return drawingBox.asString(originalRep);
    	} catch (EmptyContainerException e) {
    		System.out.println(e.getContainer());
    		if (e.getParent().equals("Circle") && e.getContainer().equals("Label"))
    			JOptionPane.showMessageDialog(this, "A circle is missing a label.", "Error", JOptionPane.INFORMATION_MESSAGE);
    		System.out.println(e.getMessage());
    		return null;
    	} catch (InvalidShapeException e) {
    		JOptionPane.showMessageDialog(this, e.getShape() + " is invalid (shown by the red outline).", "Error", JOptionPane.INFORMATION_MESSAGE);
    		System.out.println(e.getMessage());
    		return null;
    	}
    }

    private void initComponents() {
    	setBackground(Color.WHITE);
    }
    
    public BufferedImage createImage() {
        BufferedImage bufferedImage = new BufferedImage(getWidth(), getHeight(), BufferedImage.TYPE_INT_RGB);
        Graphics2D g = bufferedImage.createGraphics();
        paint(g);
        return bufferedImage;
    }
}
