package spiderdrawer.shape;

import spiderdrawer.shape.interfaces.Shape;

import java.util.ArrayList;

public class Arrays {

	public static Box[] boxArray(ArrayList<Shape> shapeList) {
		ArrayList<Box> boxList = new ArrayList<Box>();
		for (int i = 0; i < shapeList.size(); i++) {
			if (shapeList.get(i) instanceof Box) {
				boxList.add((Box) shapeList.get(i));
			}
		}
		return boxList.toArray(new Box[0]);
	}
	
	public static Circle[] circleArray(ArrayList<Shape> shapeList) {
		ArrayList<Circle> circleList = new ArrayList<Circle>();
		for (int i = 0; i < shapeList.size(); i++) {
			if (shapeList.get(i) instanceof Circle) {
				circleList.add((Circle) shapeList.get(i));
			}
		}
		return circleList.toArray(new Circle[0]);
	}
	
	public static Connective[] connectiveArray(ArrayList<Shape> shapeList) {
		ArrayList<Connective> connectiveList = new ArrayList<Connective>();
		for (int i = 0; i < shapeList.size(); i++) {
			if (shapeList.get(i) instanceof Connective) {
				connectiveList.add((Connective) shapeList.get(i));
			}
		}
		return connectiveList.toArray(new Connective[0]);
 	}
	
	 public static ArrayList<Freeform> freeformList(ArrayList<Shape> shapeList) {
	    	ArrayList<Freeform> freeforms = new ArrayList<Freeform>();
	    	for (int i = 0; i < shapeList.size(); i++) {
	    		if (shapeList.get(i) instanceof Freeform) {
	    			freeforms.add((Freeform) shapeList.get(i));
	    		}
	    	}
	    	return freeforms;
	    }
	
	public static Label[] labelArray(ArrayList<Shape> shapeList) {
		ArrayList<Label> labelList = new ArrayList<Label>();
		for (int i = 0; i < shapeList.size(); i++) {
			if (shapeList.get(i) instanceof Label) {
				labelList.add((Label) shapeList.get(i));
			}
		}
		return labelList.toArray(new Label[0]);
 	}
	
	public static Line[] lineArray(ArrayList<Shape> shapeList) {
		ArrayList<Line> lineList = new ArrayList<Line>();
		for (int i = 0; i < shapeList.size(); i++) {
			if (shapeList.get(i) instanceof Line) {
				lineList.add((Line) shapeList.get(i));
			}
		}
		return lineList.toArray(new Line[0]);
 	}
	
	public static Point[] pointArray(ArrayList<Shape> shapeList) {
		ArrayList<Point> pointList = new ArrayList<Point>();
		for (int i = 0; i < shapeList.size(); i++) {
			if (shapeList.get(i) instanceof Point) {
				pointList.add((Point) shapeList.get(i));
			}
		}
		return pointList.toArray(new Point[0]);
 	}
	
	public static Shading[] shadingArray(ArrayList<Shape> shapeList) {
		ArrayList<Shading> shadingList = new ArrayList<Shading>();
		for (int i = 0; i < shapeList.size(); i++) {
			if (shapeList.get(i) instanceof Shading) {
				shadingList.add((Shading) shapeList.get(i));
			}
		}
		return shadingList.toArray(new Shading[0]);
 	}
}
