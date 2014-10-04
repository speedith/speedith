package spiderdrawer.shape.interfaces;

import java.awt.Graphics2D;

public interface Drawable extends Shape {

	public void draw(Graphics2D g2);
	public boolean isValid();
}
