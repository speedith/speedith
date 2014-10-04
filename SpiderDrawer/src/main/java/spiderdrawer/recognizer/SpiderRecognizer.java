package spiderdrawer.recognizer;

import java.awt.Rectangle;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

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
import spiderdrawer.shape.interfaces.Shape;
import static spiderdrawer.Parameters.*;


public class SpiderRecognizer {

    private final ArrayList<Shape> shapeList;
    private final TessRecognizer tessRecognizer = new TessRecognizer();
    
    public SpiderRecognizer(ArrayList<Shape> shapeList) {
    	this.shapeList = shapeList;
    }
	
	public boolean closeToUnconnectedBox(Freeform[] freeforms) {
		Freeform freeform = new Freeform(freeforms);
		Box[] boxes = Arrays.boxArray(shapeList);
		Box box = freeform.computeOuterBox(boxes);
		Box[] innerBoxes = box.getInnerBoxes();
		for (int i = 0; i < innerBoxes.length; i++) {
			if (freeform.leftDistance(innerBoxes[i]) < CONNECTIVE_BOX_DIST_REC) {
				return true;
			}
			if (freeform.rightDistance(innerBoxes[i]) < CONNECTIVE_BOX_DIST_REC) {
				return true;
			}
		}
		return false;
	}
	
	public boolean closeToUnlabeledCircle(Freeform[] freeforms) {
		Freeform freeform = new Freeform(freeforms);
		Point center = new Point((freeform.minX()+freeform.maxX())/2, (freeform.minY()+freeform.maxY())/2);
		Circle[] circles = Arrays.circleArray(shapeList);
		for (int i = 0; i < circles.length; i++) {
			if (circles[i].hasLabel())
				continue;
			double dist = circles[i].signedDistance(center);
			if (dist < LABEL_CIRCLE_DIST) {
				return true;
			}
		}
		return false;
	}
	
	public static boolean isTextSize(Freeform[] freeforms) {
		return (isLetterSize(freeforms) || isConnectiveSize(freeforms)) && !isAnyDotSize(freeforms);
	}
	
	public static boolean isAnyDotSize(Freeform[] freeforms) {
		for (int i = 0; i < freeforms.length; i++) {
			if (freeforms[i].isDotSize())
				return true;
		}	
		return false;
	}
	
	
	
	public static boolean isLetterSize(Freeform[] freeforms) {
		Rectangle rect = surroundingRectangle(freeforms);
		if (rect.width > MAX_TEXT_WIDTH || rect.height > MAX_TEXT_HEIGHT)
			return false;
		return true;	
	}
	
	public static boolean isConnectiveSize(Freeform[] freeforms) {
		Rectangle rect = surroundingRectangle(freeforms);
		if (rect.width > MAX_CONNECTIVE_WIDTH || rect.height > MAX_CONNECTIVE_HEIGHT)
			return false;
		return true;
	}
	public static Rectangle surroundingRectangle(Freeform[] freeforms) {
		int minX = Integer.MAX_VALUE;
    	int minY = Integer.MAX_VALUE;
    	int maxX = Integer.MIN_VALUE;
    	int maxY = Integer.MIN_VALUE;
    	for (int i = 0; i < freeforms.length; i++) {
    		int currentMinX = freeforms[i].minX();
    		if (currentMinX < minX) {
    			minX = currentMinX; 
    		}
    		int currentMinY = freeforms[i].minY();
    		if (currentMinY < minY) {
    			minY = currentMinY; 
    		}
    		int currentMaxX = freeforms[i].maxX();
    		if (currentMaxX > maxX) {	
    			maxX = currentMaxX; 
    		}
    		int currentMaxY = freeforms[i].maxY();
    		if (currentMaxY > maxY) {
    			maxY = currentMaxY; 
    		}
    	}    
    	return new Rectangle(minX, minY, maxX - minX, maxY - minY);
	}
	
	public Shape checkLine(Freeform freeform) {
		Shape shape = Line.create(freeform, null);
		double len = ((Line) shape).length();
		if (len < 1) {
			System.out.println("Line is too short: deleting");
			shape =  null;
		} else if (len < 10) {
			System.out.println("Line is too short: converting to Point");
			shape = Point.create(freeform, shapeList);
		} else if (len <= MAX_LETTER_I_LEN &&  ((Line) shape).isVertical()) {
			System.out.println("Line is vertical: converting to Label I");
			Freeform[] initialArr = {freeform};
			Rectangle rect = SpiderRecognizer.surroundingRectangle(initialArr);
			shape = Label.create('I',  new Point((int)rect.getCenterX(), (int)rect.getCenterY()), shapeList);
		} else {
			shape = Line.create(freeform, shapeList);
		}
		System.out.println("len: "+ len);
		return shape;
	}
	
	public Shape checkShading(Freeform freeform) {
		Shape shape;
		Freeform[] arrFreeform = {freeform};
		if (closeToUnconnectedBox(arrFreeform)) {
			shape = checkText(freeform, true, false);
			System.out.println("Shading is not allowed here: converting to connective");
		} else {
			shape = Shading.create(freeform, shapeList);
		}
		return shape;
	}
	
	 public Shape checkText(Freeform freeform, boolean connective, boolean letter) {
	    	Freeform[] freeforms = intersectingFreeforms(freeform);
			
	    	if (closeToUnlabeledCircle(freeforms)) {
	    		System.out.println("closeToUnlabeledCircle");
	    		letter = true;
	    		connective = false;
	    	} else if (closeToUnconnectedBox(freeforms)) {
	    		System.out.println("closeToUnconnectedBox");
	    		letter = false;
	    		connective = true;
	    	}
	    	
	    	Rectangle rect = SpiderRecognizer.surroundingRectangle(freeforms);
			Character character = (connective)? ((letter)? tessRecognizer.classifyText(freeforms) : tessRecognizer.classifyConnective(freeforms)) : tessRecognizer.classifyLetter(freeforms);
			if (!freeform.isLast(freeforms)) {
				System.out.println("More being drawn...");
				return null;
			}
			Shape shape = null;
			if (character != null) {
				Point center = new Point((int)rect.getCenterX(), (int)rect.getCenterY());
				if (Character.isAlphabetic((int) character))
					shape = Label.create(character, center, shapeList);
				else 
					shape = Connective.create(Logical.create(character), center, shapeList);
			}
			for (int i = 0; i < freeforms.length; i++)
				shapeList.remove(freeforms[i]);
			return shape;
	    }
	 
	 private Freeform[] intersectingFreeforms(Freeform f) {
	    	Set<Freeform> intersectingFreeforms = f.overlappingFreeforms(Arrays.freeformList(shapeList), new HashSet<Freeform>());
	    	return intersectingFreeforms.toArray(new Freeform[0]);
	 }
}
