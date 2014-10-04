package spiderdrawer.shape;

import java.awt.Color;
import java.awt.Graphics2D;
import java.util.ArrayList;

import spiderdrawer.shape.containers.MultiContainer;
import spiderdrawer.shape.containers.SingleContainer;
import spiderdrawer.shape.interfaces.Deletable;
import spiderdrawer.shape.interfaces.Drawable;
import spiderdrawer.shape.interfaces.Movable;
import spiderdrawer.shape.interfaces.Shape;
import static spiderdrawer.Parameters.*;

public class Circle implements Drawable, Movable, Deletable {

	Point center;
	int radius;
	private ArrayList<Shape> shapeList;
	SingleContainer<Label, Circle> label;
	boolean moveLabel;
	MultiContainer<Point, Circle> points;
	MultiContainer<Shading, Circle> shadings;
	public MultiContainer<Box, Circle> boxes;
	MultiContainer<Box, Circle> innerBoxes;
	MultiContainer<Box, Circle> overlapBoxes;
	MultiContainer<Circle, Circle> overlapCircles;
	
	public Circle(Point center, int radius) {
		this.center = center;
		this.radius = radius;
		createContainers();
	}
	
	public Circle(int centerX, int centerY, int radius) {
		this(new Point(centerX, centerY), radius);
	}
	
	private void createContainers() {
		label = new SingleContainer<Label, Circle>(this);
		points = new MultiContainer<Point, Circle>(this);
		shadings = new MultiContainer<Shading, Circle>(this);
		boxes = new MultiContainer<Box, Circle>(this);
		innerBoxes = new MultiContainer<Box, Circle>(this);
		overlapBoxes = new MultiContainer<Box, Circle>(this);
		overlapCircles = new MultiContainer<Circle, Circle>(this);
	}
	
	public static Circle create(int centerX, int centerY, int radius, ArrayList<Shape> shapeList) {
		radius = Math.max(radius,MIN_CIRCLE_RADIUS);
		Circle circle = new Circle(centerX, centerY, radius);
		circle.createContainers();
		circle.shapeList = shapeList;
		circle.recompute(false);
		return circle;
	}
	
	public static Circle create(Freeform freeform, ArrayList<Shape> shapeList) {
		int x = (freeform.minX() + freeform.maxX())/2;
		int y = (freeform.minY() + freeform.maxY())/2;
		int r = (x - freeform.minX() + y - freeform.minY())/2;
		return create(x, y, r, shapeList);
	}
	
	public Point getCenter() {
		return center;
	}
	
	public int getRadius() {
		return radius;
	}
	
	public boolean hasLabel() {
		return label.get() != null;
	}
	
	
	protected boolean contains(Freeform freeform) {
		if (freeform.points.size() < 2)
			return false;
		
		for (int i = 0; i < freeform.points.size()-1; i++) {
			Point p1 = freeform.points.get(i);
			Point p2 = freeform.points.get(i+1);
			if (this.distance(new Line(p1, p2)) > 0) {
				return false;
			}
		}
		
		return true;
	}
	
	protected boolean contains(Line line) {
		return (contains(line.start) && contains(line.end));
	}
	
	protected boolean contains(Point point) {
		return (center.distance(point) < radius);
	}
	
	protected boolean contains(Box box) {
		return this.contains(box.getTopLeft()) && this.contains(box.topRight()) && this.contains(box.bottomLeft()) && this.contains(box.bottomRight());
		
	}
	
	protected double distance(Freeform freeform) {
		double minDist = Double.MAX_VALUE;
		for (int i = 0; i < freeform.points.size()-1; i++) {
			Point p1 = freeform.points.get(i);
			Point p2 = freeform.points.get(i+1);
			double dist = this.distance(new Line(p1, p2));
			if (dist < minDist) {
				minDist = dist;
			}
		}
		return minDist;
	}
	
	protected double distance(Line l) {
		return l.distance(this);
	}
	
	protected double distance(Point p) {
		return Math.max(0, signedDistance(p));
	}
	
	public double boundaryDistance(Point p) {
		return Math.abs(signedDistance(p));
	}
	
	public double signedDistance(Point p) {
		return center.distance(p) - radius;
	}
		
	public double distance(Label label) {
		return label.distance(this);
	}
	
	public double signedDistance(Label label) {
		return label.signedDistance(this);
	}
	
	public String asString() {
		return center.x + "," + center.y + "," + radius;
	}
	
	@Override
	public boolean isValid() {
		return hasLabel() && overlapBoxes.isEmpty() && innerBoxes.isEmpty();
	}
		
	@Override
	public void draw(Graphics2D g2) {
		if (!isValid()) {
			g2.setColor(Color.RED);
		} else {
			g2.setColor(Color.BLACK);
		}
		g2.drawOval((int)(center.getX()-radius), (int)(center.getY()-radius), radius*2, radius*2);
		g2.setColor(Color.BLACK);
	}
	
	public void move(Point from, Point to, boolean external) {
		if (external) {
			center.move(from, to);
			if (label.get() != null) {
				if (moveLabel) {
					label.get().move(from, to);
				} else if (label.get().distance(this) > LABEL_CIRCLE_DIST) {
					label.set(null, null);
				}		
			}
		} else {
			move(from, to, false);
		}
	}

	@Override
	public void move(Point from, Point to) {
		move(from, to, true);
		if (points != null) {
			for (int i = 0; i < points.size(); i++) {
				points.get(i).move(from, to);
			}
		}
		
	}
	
	protected void computeLabels(Label[] labels) {
		int labelPos = -1;
		double lowestDist = Double.MAX_VALUE;
		for (int i = 0; i < labels.length; i++) {
			if (labels[i].circle.get() != null)
				continue;
			double dist = this.distance(labels[i]);
			if (dist < lowestDist) {
				lowestDist = dist;
				labelPos = i;
			}
		}
		if (label.get() == null && lowestDist <= LABEL_CIRCLE_DIST && labelPos != -1) {
			label.set(labels[labelPos], labels[labelPos].circle);
			moveLabel = false;
		}
	}
	
	private void computePoints(Point[] points) {
		this.points.removeAll();
		for (int i = 0; i < points.length; i++) {
			if (this.distance(points[i]) == 0) {
				this.points.add(points[i], points[i].circles);
			}
		}
	}
	
	private void computeBoxes(Box[] boxes) {
		this.boxes.removeAll();
		for (int i = 0; i < boxes.length; i++) {
			if (boxes[i].contains(this) && !boxes[i].innerBoxesContains(this)) {
				this.boxes.add(boxes[i], boxes[i].circles);
			}
		}
		/* Inner Boxes */
		innerBoxes.removeAll();
		for (int i = 0; i < boxes.length; i++) {
			if (this.contains(boxes[i])) {
				innerBoxes.add(boxes[i], boxes[i].outerCircles);
			}
		}
	}
	
	
	private void computeOverlapBoxes(Box[] boxes) {
		overlapBoxes.removeAll();
		for (int i = 0; i < boxes.length; i++) {
			if (boxes[i].intersects(this)) {
				overlapBoxes.add(boxes[i], boxes[i].overlapCircles);
			}
		}
	}
	
	private void computeOverlapCircles(Circle[] circles) {
		overlapCircles.removeAll();
		for (int i = 0; i < circles.length; i++) {
			if (circles[i].intersects(this))
				overlapCircles.add(circles[i], circles[i].overlapCircles);
		}
	}

	@Override
	public void recompute(boolean moving) {
		if (shapeList == null)
			return;
		if (!moving) {
			computeLabels(Arrays.labelArray(shapeList));
			computePoints(Arrays.pointArray(shapeList));
		}
		computeOverlapBoxes(Arrays.boxArray(shapeList));
		computeOverlapCircles(Arrays.circleArray(shapeList));
		computeBoxes(Arrays.boxArray(shapeList));
		if (!moving) {
			moveLabel = true;
		}
		if (!moving && hasLabel()) {
			label.get().snapToCircle(this);
		}
	}

	@Override
	public boolean isWithin(Point p) {
		return Math.abs(center.distance(p)-radius) < CIRCLE_MIN_DIST;
	}
	/*
	 * Method: solve t^2(d.d)+2t(d.(s-c)) + (s-c).(s-c) - r^2 = 0
	 *	check t1 or t2 between 0 and 1.
	 */
	@Override
	public boolean intersects(Line line) {
		Point d = line.end.minus(line.start);
		if (d.x == 0 && d.y == 0) {
			return line.start.distance(center) == radius;
		}
		Point sMc = line.start.minus(center);
		double a = d.dot(d);
		double b = 2*d.dot(sMc);
		double c = sMc.dot(sMc) - radius*radius;
		
		double disc = b*b-4*a*c;
		if (disc < 0)	//Imaginary solutions
			return false;
		
		double sqrt_disc = Math.sqrt(disc);
		
		double t1 = (-b + sqrt_disc)/(2*a);
		if (t1 >= 0 && t1 <= 1)
			return true;
		
		double t2 = (-b - sqrt_disc)/(2*a);
		if (t2 >= 0 && t2 <= 1)
			return true;
		
		return false;
	}
	
	public boolean intersects(Freeform freeform) {
		return freeform.intersects(this);
	}
	
	public boolean intersects(Circle circle) {
		return (center.distance(circle.center) <= radius + circle.radius);
	}

	@Override
	public void remove() {
		label.set(null, null);
		if (points != null) {
			for (int i = 0; i < points.size(); i++) {
				points.get(i).recompute(false);
			}
		}
		points.removeAll();
		shadings.removeAll();
		boxes.removeAll();
		innerBoxes.removeAll();
		overlapBoxes.removeAll();
		overlapCircles.removeAll();
	}
}
