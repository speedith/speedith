package spiderdrawer.shape.interfaces;

import spiderdrawer.shape.Point;

public interface Movable extends Shape {
		
	public void move(Point from, Point to);
	public void recompute(boolean moving);
	public boolean isWithin(Point p);
	public double boundaryDistance(Point p);
}
