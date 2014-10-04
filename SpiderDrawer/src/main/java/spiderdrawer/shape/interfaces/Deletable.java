package spiderdrawer.shape.interfaces;

import spiderdrawer.shape.Line;

public interface Deletable extends Shape {
	
	public boolean intersects(Line line);
	public void remove();
}
