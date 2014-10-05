package spiderdrawer;

import static org.junit.Assert.*;

import org.junit.Ignore;
import org.junit.Test;

import spiderdrawer.shape.Circle;
import spiderdrawer.shape.Freeform;
import spiderdrawer.shape.Line;
import spiderdrawer.shape.Point;

public class IntersectsTest {

	@Test
	public void doIntersect() {	
		Line line1 = new Line(4,5, 15,12);
		Line line2 = new Line(14,4, 9,15);
		assertTrue(line1.intersects(line2));
	}
	
	@Test
	public void dontIntersect() {	
		Line line1 = new Line(4,5, 15,12);
		Line line2 = new Line(14,4, 15,9);
		assertFalse(line1.intersects(line2));
	}
	
	
	@Test
	public void twoPointsOverlap() {
		Line line1 = new Line(4,5, 4,5);
		Line line2 = new Line(4,5, 4,5);
		assertTrue(line1.intersects(line2));
	}
	
	@Test
	public void twoPointsDontOverlap() {
		Line line1 = new Line(4,5, 4,5);
		Line line2 = new Line(4,2, 4,2);
		assertFalse(line1.intersects(line2));
	}
	
	@Test
	public void firstVerticalDoOverlap() {
		Line line1 = new Line(4,5, 4,15);
		Line line2 = new Line(0,5, 10,10);
		assertTrue(line1.intersects(line2));
	}
	
	@Test
	public void firstVerticalDontOverlap() {
		Line line1 = new Line(4,8, 4,15);
		Line line2 = new Line(0,5, 10,10);
		assertFalse(line1.intersects(line2));
	}
	
	@Test
	public void secondVerticalDoOverlap() {
		Line line1 = new Line(0,5, 10,10);
		Line line2 = new Line(4,5, 4,15);
		assertTrue(line1.intersects(line2));
	}
	
	@Test
	public void secondVerticalDontOverlap() {
		Line line1 = new Line(0,5, 10,10);
		Line line2 = new Line(4,8, 4,15);
		assertFalse(line1.intersects(line2));
	}

	@Test
	public void bothVerticalDoOverlap() {
		Line line1 = new Line(4,1, 4,5);
		Line line2 = new Line(4,5, 4,15);
		assertTrue(line1.intersects(line2));
	}
	
	@Test
	public void bothVerticalSeperateDontOverlap() {
		Line line1 = new Line(5,1, 5,5);
		Line line2 = new Line(5,6, 5,15);
		assertFalse(line1.intersects(line2));
	}
	
	@Test
	public void bothVerticalDontOverlap() {
		Line line1 = new Line(4,1, 4,4);
		Line line2 = new Line(4,5, 4,15);
		assertFalse(line1.intersects(line2));
	}
	
	@Test
	public void parallelDoOverlap() {
		Line line1 = new Line(4,1, 12,9);
		Line line2 = new Line(0,-3, 4,1);
		assertTrue(line1.intersects(line2));
	}
	
	@Test
	public void parallelDontOverlap() {
		Line line1 = new Line(4,1, 12,9);
		Line line2 = new Line(13,10, 20,17);
		assertFalse(line1.intersects(line2));
	}
	
	@Test
  @Ignore
	public void circleIntersects() {
		Circle circle = new Circle(369, 348, 90);
		Line l = new Line(new Point(368,259), new Point(369,259));
		assertTrue(circle.intersects(l));
	}
}
