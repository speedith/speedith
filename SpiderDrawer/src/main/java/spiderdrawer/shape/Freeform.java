package spiderdrawer.shape;

import java.awt.Graphics2D;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

import spiderdrawer.shape.interfaces.Deletable;
import spiderdrawer.shape.interfaces.Drawable;
import static spiderdrawer.Parameters.FREEFORM_OVERLAP_DIST;
import static spiderdrawer.Parameters.MAX_DOT_HEIGHT;
import static spiderdrawer.Parameters.MAX_DOT_WIDTH;

public class Freeform implements Drawable, Deletable {

	ArrayList<Point> points;
	boolean removed;
	
	public Freeform() {
		this.points = new ArrayList<Point>();
		removed = false;
	}
	
	public Freeform(ArrayList<Point> points) {
		this.points = points;
		removed = false;
	}
	
	public Freeform(Freeform[] freeforms) {
		this.points = new ArrayList<Point>();
		for (int i = 0; i < freeforms.length; i++)
			this.points.addAll(freeforms[i].points);
	}
	
	public Freeform(Point point) {
		this(new ArrayList<Point>());
		points.add(point);
	}
	
	public Freeform(int pointX, int pointY) {
		this(new Point(pointX, pointY));
	}
	
	public void addPoint(Point point) {
		points.add(point);
	}
	
	public void addPoint(int pointX, int pointY) {
		points.add(new Point(pointX, pointY));
	}
	
	public ArrayList<Point> getPoints() {
		return points;
	}
	
	public String pointsAsString() {
		StringBuilder sb = new StringBuilder();
		for (int i = 0; i < points.size(); i++) {
			sb.append(points.get(i).x + "," + points.get(i).y);
			if (i != points.size() - 1) {
				sb.append(',');
			}
		}
		return sb.toString();
	}
	
	/*
	 * Whether the freeform object is within distance of this freeform.
	 * @Returns boolean.
	 */
	public boolean overlaps(Freeform freeform, int distance) {
		ArrayList<Point> comparedPoints = freeform.getPoints();
		for (int i = 0; i < points.size() - 1; i++) {
			Line pLine = new Line(points.get(i), points.get(i+1));
			for (int j = 0; j < comparedPoints.size() - 1; j++) {
				if (pLine.distance(new Line(comparedPoints.get(j), comparedPoints.get(j+1))) <= distance) {
					return true;
				}
			}
		}
		return false;
	}
	
    public ArrayList<Freeform> getOverlappingFreeforms(ArrayList<Freeform> freeforms) {
    	ArrayList<Freeform> overlappingFreeforms = new ArrayList<Freeform>();
    	for (int i = 0; i < freeforms.size(); i++) {
			Freeform currentFF = (Freeform) freeforms.get(i);
			if (!this.equals(currentFF) && this.overlaps(currentFF, FREEFORM_OVERLAP_DIST)) {
				overlappingFreeforms.add(currentFF);
			}
    	}
    	return overlappingFreeforms;
    }
	
	public int minX() {
		int result = Integer.MAX_VALUE;
		for(int i = 0; i < points.size(); i++) {
			int value = points.get(i).getX();
			if (value < result) {
				result = value;
			}
		}
		return result;
	}
	
	public int maxX() {
		int result = Integer.MIN_VALUE;
		for(int i = 0; i < points.size(); i++) {
			int value = points.get(i).getX();
			if (value > result) {
				result = value;
			}
		}
		return result;
	}
	
	public int minY() {
		int result = Integer.MAX_VALUE;
		for(int i = 0; i < points.size(); i++) {
			int value = points.get(i).getY();
			if (value < result) {
				result = value;
			}
		}
		return result;
	}
	
	public int maxY() {
		int result = Integer.MIN_VALUE;
		for(int i = 0; i < points.size(); i++) {
			int value = points.get(i).getY();
			if (value > result) {
				result = value;
			}
		}
		return result;
	}
	
	@Override
	public boolean isValid() {
		return true;
	}
	
	public void draw(Graphics2D g2) {
		for (int i = 0; i < points.size() - 1; i++) {
            Point p1 = points.get(i);
            Point p2 = points.get(i+1);

            g2.drawLine(p1.x, p1.y, p2.x, p2.y);
        }
	}
	
	public Box computeOuterBox(Box[] boxes) {
		for (int i = 0; i < boxes.length; i++) {
			if (boxes[i].contains(this) && !boxes[i].innerBoxesContains(this)) {
				return boxes[i];
			}
		}
		return null;
	}

	@Override
	public boolean intersects(Line line) {
		boolean overlaps = false;
		for (int i = 0; i < points.size() - 1; i++) {
            Point p1 = points.get(i);
            Point p2 = points.get(i+1);
            Line currentLine = new Line(p1, p2);
            if (currentLine.intersects(line)) {
            	overlaps = true;
            	break;
            }
		}
		return overlaps;
	}
	
	public boolean intersects(Circle circle) {
		for (int i = 0; i < points.size()-1; i++) {
			Line line = new Line(points.get(i), points.get(i+1));
			if (circle.intersects(line))
				return true;
		}
		return false;
	}
	
    public Set<Freeform> overlappingFreeforms(ArrayList<Freeform> freeformList, Set<Freeform> currentFreeforms) {
    	Set<Freeform> intersectingFreeforms = new HashSet<Freeform>();
    	intersectingFreeforms.add(this);
    	currentFreeforms.add(this);
    	ArrayList<Freeform> currentOverlappingFreeforms = this.getOverlappingFreeforms(freeformList);
    	for (int i = 0; i < currentOverlappingFreeforms.size(); i++) {
    		if (!intersectingFreeforms.contains(currentOverlappingFreeforms.get(i)) && !currentFreeforms.contains(currentOverlappingFreeforms.get(i))) {
    			intersectingFreeforms.addAll(currentOverlappingFreeforms.get(i).overlappingFreeforms(freeformList, currentFreeforms));
    		}
    	}
    	return intersectingFreeforms;
    }
    
    public double leftDistance(Box box) { //Swap left and right because change of perspective.
		return box.rightDistance(this);
	}
	
	public double rightDistance(Box box) { //Swap left and right because change of perspective.
		return box.leftDistance(this);
	}
	
	public boolean isRemoved() {
		return removed;
	}
	
	public boolean isDotSize() {
		if (maxX() - minX() > MAX_DOT_WIDTH || maxY() - minY() > MAX_DOT_HEIGHT)
			return false;
		return true;
	}

	@Override
	public void remove() {
		removed = true;
	}
	
	public boolean isLast(Freeform[] freeforms) {
		for (int i = 0; i < freeforms.length; i++) {
			if (freeforms[i].points.get(0).time > points.get(0).time)
				return false;
		}
		return true;
	}
}
