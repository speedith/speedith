package spiderdrawer.shape;

import static spiderdrawer.Parameters.*;

import java.awt.Canvas;
import java.awt.Color;
import java.awt.Font;
import java.awt.Graphics2D;
import java.util.ArrayList;

import javax.swing.UIManager;

import spiderdrawer.shape.containers.SingleContainer;
import spiderdrawer.shape.interfaces.Deletable;
import spiderdrawer.shape.interfaces.Drawable;
import spiderdrawer.shape.interfaces.Movable;
import spiderdrawer.shape.interfaces.Shape;

public class Connective implements Drawable, Movable, Deletable {
	
	Logical logical;
	Point center;
	int width;
	int height;
	private ArrayList<Shape> shapeList;
	SingleContainer<Box, Connective> leftBox;
	SingleContainer<Box, Connective> rightBox;
	SingleContainer<Box, Connective> outerBox;
	
	public Connective(Logical logical, Point center) {
		this.logical = logical;
		this.center = center;
		setHeightAndWidth();
	}
	
	private void createContainers() {
		leftBox = new SingleContainer<Box, Connective>(this);
		rightBox = new SingleContainer<Box, Connective>(this);
		outerBox = new SingleContainer<Box, Connective>(this);
	}
	
	public static Connective create(Logical logical, Point center, ArrayList<Shape> shapeList) {
		Connective connective = new Connective(logical, center);
		connective.createContainers();
		connective.shapeList = shapeList;
		connective.recompute(false);
		return connective;
	}
	
	public static Connective create(Logical logical, int x, int y, ArrayList<Shape> shapeList) {
		return create(logical, new Point(x, y), shapeList);
	}
	
	private char asChar() {
		switch (logical) {
			case EQUIVALENCE: return '\u2194';
			case IMPLICATION: return '\u2192';
			case DISJUNCTION: return '\u2228';
			case CONJUNCTION: return '\u2227';
			case NEGATION:	  return '\u00AC';
			default: return '\0';
		}
	}
	
	public String asString() {
		switch (logical) {
			case EQUIVALENCE: return "<-->";
			case IMPLICATION: return "-->";
			case DISJUNCTION: return "|";
			case CONJUNCTION: return "&";
			case NEGATION:	  return "not";
			default: return "";
		}
	}

	
	private void setHeightAndWidth() {
		Font font = new Font(UIManager.getDefaults().getFont("TabbedPane.font").getFontName(), Font.PLAIN, CONNECTIVE_FONT_SIZE);
		Canvas c = new Canvas();
		width = c.getFontMetrics(font).stringWidth(Character.toString(this.asChar())) - 3;
		height = c.getFontMetrics(font).getAscent()/2;
	}
	
	protected boolean isFullyConnected() {
		if (logical == Logical.NEGATION) {
			return (rightBox.get() != null);
		}
		return (leftBox.get() != null) && (rightBox.get() != null);
	}
	
	public Box getLeftBox() {
		return leftBox.get(); 
	}
	
	public Box getRightBox() {
		return rightBox.get();
	}
	
	@Override
	public boolean isValid() {
		return isFullyConnected();
	}

	@Override
	public void draw(Graphics2D g2) {
		char[] array = new char[1];
		array[0] = this.asChar();
		if (!isValid()) {
			g2.setColor(Color.RED);
		} else {
			g2.setColor(Color.BLACK);
		}
			
		g2.setFont(new Font(g2.getFont().getFontName(), Font.PLAIN, CONNECTIVE_FONT_SIZE));
		if (logical == Logical.EQUIVALENCE || logical == Logical.IMPLICATION || logical == Logical.NEGATION) //Shift it down by 5, due to dimensions bug.
			g2.drawChars(array, 0, 1, center.getX() - width/2, center.getY() + 5 + height/2);
		else
			g2.drawChars(array, 0, 1, center.getX() - width/2, center.getY() + height/2);
		if (logical == Logical.DISJUNCTION) {
			array[0] = 'C';
			g2.setFont(new Font(g2.getFont().getFontName(), Font.PLAIN, 10));
			g2.drawChars(array, 0, 1, center.getX() + width/4, center.getY() + height/2 + 5);
		}
		
		g2.setColor(Color.BLACK);
	}

	
	public void move(Point from, Point to, boolean external) {
		if (external) {
			center.move(from, to);
			if (leftBox.get() != null)
				leftBox.get().move(from, to, true);
			rightBox.get().move(from, to, true);
		} else {
			move(from, to);
		}
	}
	
	@Override
	public void move(Point from, Point to) {
		center.move(from, to);
		if (leftBox.get() != null && this.leftDistance(leftBox.get()) > CONNECTIVE_BOX_DIST) {
			leftBox.set(null, null);
		}
		if (rightBox.get() != null && this.rightDistance(rightBox.get()) > CONNECTIVE_BOX_DIST) {
			rightBox.set(null, null);
		}
	}

	
	public void computeBoxes(Box[] boxes) {
		int leftBoxPos = -1;
		int rightBoxPos = -1;
		double lowestLeftDist = Double.MAX_VALUE;
		double lowestRightDist = Double.MAX_VALUE;
		for (int i = 0; i < boxes.length; i++) {
			if (boxes[i].connective.get() != null)
				continue;
			double leftDist = this.leftDistance(boxes[i]);
			double rightDist = this.rightDistance(boxes[i]);
			if (leftDist < lowestLeftDist) {
				lowestLeftDist = leftDist;
				leftBoxPos = i;
			}
			if (rightDist < lowestRightDist) {
				lowestRightDist = rightDist;
				rightBoxPos = i;
			}
		}
		
		if (this.logical == Logical.NEGATION) //If negation, then can only have right box.
			leftBoxPos = -1;
		
		if (leftBox.get() == null) {
			if (/*(lowestLeftDist <= CONNECTIVE_BOX_DIST &&*/ leftBoxPos != -1) {
				System.out.println("close to leftBox");
				leftBox.set(boxes[leftBoxPos], boxes[leftBoxPos].connective);
				boxes[leftBoxPos].leftConnective = false;
			}
		}
		if (rightBox.get() == null) {
			if (/*lowestRightDist <= CONNECTIVE_BOX_DIST &&*/ rightBoxPos != -1) {
				System.out.println("close to rightBox");
				rightBox.set(boxes[rightBoxPos], boxes[rightBoxPos].connective);
				boxes[rightBoxPos].leftConnective = true;
			}
		}
	}
	
	public void computeOuterBoxes(Box[] boxes) {
		if (outerBox.get() != null)
			outerBox.set(null, null);
		for (int i = 0; i < boxes.length; i++) {
			if (boxes[i].contains(this) && !boxes[i].innerBoxesContains(this)) {
				outerBox.set(boxes[i], boxes[i].innerConnectives);
				break;
			}
		}
	}

	@Override
	public void recompute(boolean moving) {
		if (shapeList == null)
			return;
		computeBoxes(Arrays.boxArray(shapeList));
		computeOuterBoxes(Arrays.boxArray(shapeList));
	}
	
	public double boundaryDistance(Point p) {
		Box box = new Box(center.x - width/2, center.y - height/2, width, height);
		return box.distance(p);
	}
	
	protected double distance(Box box) {
		return box.distance(this);
	}
	
	protected double leftDistance(Box box) { //Swap left and right because change of perspective.
		return box.rightDistance(this);
	}
	
	protected double rightDistance(Box box) { //Swap left and right because change of perspective.
		return box.leftDistance(this);
	}

	@Override
	public boolean isWithin(Point p) {
		return ((Math.abs(p.getX() - center.getX()) < (double)width/2) && (Math.abs(p.getY() - center.getY()) < (double)height/2));
	}

	@Override
	public boolean intersects(Line line) {
		Box box = new Box(center.x - width/2, center.y - height/2, width, height);
		return box.intersects(line);
	}

	@Override
	public void remove() {
		leftBox.set(null, null);
		rightBox.set(null, null);
		outerBox.set(null, null);
	}
	
	
}
