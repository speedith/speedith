package spiderdrawer;

import java.util.ArrayList;

import org.junit.Test;

import spiderdrawer.shape.Label;
import spiderdrawer.shape.Circle;
import spiderdrawer.shape.Point;
import spiderdrawer.shape.interfaces.Shape;
import static org.junit.Assert.assertEquals;
import static spiderdrawer.Parameters.*;

public class SnapTesting {

	@Test
	public void labelToCircle() {
		Circle circle = new Circle(100, 100, 40);
		ArrayList<Shape> shapeList = new ArrayList<>(1);
		shapeList.add(circle);
		Label label = Label.create('A', new Point(circle.getCenter().getX()-10, circle.getCenter().getY()-10), shapeList);
		label.recompute(false);
		int dist = (int) ((circle.getRadius() + LABEL_CIRCLE_DISIRED_DIST)/Math.sqrt(2) + 0.5);
		assertEquals(label.getCenter().getX(), circle.getCenter().getX() - dist);
		assertEquals(label.getCenter().getY(), circle.getCenter().getY() - dist);
	}
	
	@Test
	public void labelToCircleAtCenter() {
		Circle circle = new Circle(100, 100, 40);
		ArrayList<Shape> shapeList = new ArrayList<>(1);
		shapeList.add(circle);
		Label label = Label.create('A', new Point(circle.getCenter().getX(), circle.getCenter().getY()), shapeList);
		label.recompute(false);
		int dist = (int) ((circle.getRadius() + LABEL_CIRCLE_DISIRED_DIST)/Math.sqrt(2) + 0.5);
		assertEquals(label.getCenter().getX(), circle.getCenter().getX() - dist);
		assertEquals(label.getCenter().getY(), circle.getCenter().getY() - dist);
	}
	
}
