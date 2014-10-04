package spiderdrawer;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertNotEquals;

import java.util.ArrayList;

import org.junit.Test;

import spiderdrawer.shape.Line;
import spiderdrawer.shape.Point;
import spiderdrawer.shape.interfaces.Shape;

public class SpiderTest {

	@Test
	public void createSpiderFromPoint() {
		Point point = Point.create(0, 0, new ArrayList<Shape>());
		assertNotNull(point.getSpider());
		point.getSpider().remove(point);
		assertNull(point.getSpider());
	}
	
	@Test
	public void createSpiderFromLine() {
		Line line = Line.create(0, 0, 10, 10, new ArrayList<Shape>());
		assertNotNull(line.getSpider());
		line.getSpider().remove(line);
		assertNull(line.getSpider());
	}
	
	@Test
	public void createSpiderFromLineAndPoints() {
		ArrayList<Shape> shapes = new ArrayList<Shape>();
		Line line = Line.create(0, 0, 10, 10, shapes);
		shapes.add(line);
		Point point = Point.create(0, 0, shapes);
		shapes.add(point);
		Point point2 = Point.create(10, 10, shapes);
		shapes.add(point2);
		assertNotNull(line.getSpider());
		assertEquals(line.getSpider(), point.getSpider());
		assertEquals(line.getSpider(), point2.getSpider());
		line.getSpider().remove(line);
		assertNull(line.getSpider());
		assertNotEquals(point.getSpider(), point2.getSpider());
	}
	
	@Test
	public void createSpiderFromLineAndPoints2() {
		ArrayList<Shape> shapes = new ArrayList<Shape>();
		Line line = Line.create(0, 0, 10, 10, shapes);
		shapes.add(line);
		Point point = Point.create(0, 0, shapes);
		shapes.add(point);
		Point point2 = Point.create(10, 10, shapes);
		shapes.add(point2);
		assertNotNull(line.getSpider());
		assertEquals(line.getSpider(), point.getSpider());
		assertEquals(line.getSpider(), point2.getSpider());
		point.getSpider().remove(point);
		assertNull(point.getSpider());
		assertEquals(line.getSpider(), point2.getSpider());
	}
	
	
	@Test
	public void removeMiddlePoint() {
		ArrayList<Shape> shapes = new ArrayList<Shape>();
		Line line = Line.create(0, 0, 10, 10, shapes);
		shapes.add(line);
		Point point = Point.create(0, 0, shapes);
		shapes.add(point);
		Point point2 = Point.create(10, 10, shapes);
		shapes.add(point2);
		Line line2 = Line.create(10, 10, 20, 20, shapes);
		shapes.add(line2);
		Point point3 = Point.create(20, 20, shapes);
		shapes.add(point3);
		assertNotNull(line.getSpider());
		assertEquals(line.getSpider(), point.getSpider());
		assertEquals(line.getSpider(), point2.getSpider());
		assertEquals(line.getSpider(), point3.getSpider());
		assertEquals(line.getSpider(), line2.getSpider());
		point2.getSpider().remove(point2);
		assertNull(point2.getSpider());
		assertEquals(line.getSpider(), point.getSpider());
		assertEquals(line2.getSpider(), point3.getSpider());
		assertNotEquals(point.getSpider(), point3.getSpider());
	}
}
