package spiderdrawer.shape;

import java.awt.Canvas;
import java.awt.Color;
import java.awt.Font;
import java.awt.Graphics2D;
import java.util.ArrayList;

import javax.swing.UIManager;

import spiderdrawer.shape.containers.SingleContainer;
import spiderdrawer.shape.interfaces.Deletable;
import spiderdrawer.shape.interfaces.Drawable;
import spiderdrawer.shape.interfaces.Movable;
import spiderdrawer.shape.interfaces.Shape;
import static spiderdrawer.Parameters.*;

public class Label implements Drawable, Movable, Deletable {

	char letter;
	int number;
	Point center;
	int width;
	int height;
	private ArrayList<Shape> shapeList;
	SingleContainer<Circle, Label> circle;
	SingleContainer<Box, Label> box;
	ArrayList<Label> sameLabels;
	
	/*
	 *  position is center of letter
	 */
	public Label(char letter, Point position) {
		this.letter = letter;
		this.center = position;
		setHeightAndWidth();
		this.number = 0;
	}
	
	public Label(char letter, int positionX, int positionY) {
		this(letter, new Point(positionX, positionY));
	}
	
	public Label(char letter, int number, int positionX, int positionY) {
		this(letter, positionX, positionY);
		this.number = number;
		createContainers();
	}
	
	private void createContainers() {
		circle = new SingleContainer<Circle, Label>(this);
		box = new SingleContainer<Box, Label>(this);
	}
	
	public static Label create(char letter, Point position, ArrayList<Shape> shapeList) {
		Label label = new Label(letter, position);
		label.createContainers();
		label.shapeList = shapeList;
		label.recompute(false);
		return label;
	}
	
	private void setHeightAndWidth() {
		Font font = new Font(UIManager.getDefaults().getFont("TabbedPane.font").getFontName(), Font.PLAIN, FONT_SIZE);
		Canvas c = new Canvas();
		width = c.getFontMetrics(font).stringWidth(Character.toString(letter));
		height = c.getFontMetrics(font).getAscent();
	}
	
	@Override
	public void move(Point from, Point to) {
		center.move(from, to);
		if (circle.get() != null && this.distance(circle.get()) > LABEL_CIRCLE_DIST) {
			circle.set(null, null);
		}
	}
	
	public Point getCenter() {
		return center;
	}
	
	protected char getChar() {
		return letter;
	}
	
	public String asString() {
		return letter + "," + center.x + "," + center.y;
	}
	
	public double boundaryDistance(Point p) {
		Box box = new Box(center.x - width/2, center.y - height/2, width, height);
		return box.distance(p);
	}
	
	protected double distance(Circle c) {
		return c.distance(center);
	}
	
	protected double signedDistance(Circle c) {
		return c.signedDistance(center);
	}
	
	@Override
	public boolean isWithin(Point p) {
		int width = Math.max(this.width, LABEL_MIN_WIDTH);
		return ((Math.abs(p.getX() - center.getX()) < (double)width/2) && (Math.abs(p.getY() - center.getY()) < (double)height/2));
	}
	
	
	private void computeCircles(Circle[] circles) {
		int circlePos = -1;
		double lowestDist = Double.MAX_VALUE;
		for (int i = 0; i < circles.length; i++) {
			if (circles[i].hasLabel())
				continue;
			double dist = this.signedDistance(circles[i]);
			if (dist <= LABEL_CIRCLE_DIST && Math.abs(dist) < Math.abs(lowestDist)) {
				lowestDist = dist;
				circlePos = i;
			}
		}
		if ((circle.get() == null || Math.abs(lowestDist) <  Math.abs(circle.get().signedDistance(this))) && lowestDist <= LABEL_CIRCLE_DIST && circlePos != -1) {
			circle.set(circles[circlePos], circles[circlePos].label);	
			
		}
	}
	
	@Override
	public void recompute(boolean moving) {
		if (shapeList == null)
			return;
		computeCircles(Arrays.circleArray(shapeList));
		computeBoxes(Arrays.boxArray(shapeList));
		computeLabels(Arrays.labelArray(shapeList));
		if (circle.get() != null && !moving)
			snapToCircle(circle.get());
	}
	
	public void computeBoxes(Box[] boxes) {
		int boxPos = -1;
		for (int i = 0; i < boxes.length; i++) {
			if (boxes[i].contains(this) && !boxes[i].innerBoxesContains(this)) {
				boxPos = i;
				break;
			}
		}
		
		if (boxPos != -1 && !boxes[boxPos].equals(box)) {
			box.set(boxes[boxPos], boxes[boxPos].labels);
		}
	}
	
	protected void addSameLabel(Label label) {
		if (this.sameLabels == null)
			this.sameLabels = new ArrayList<Label>();
		sameLabels.add(label);
		if (label != null && !label.containsSameLabel(this)) {
			label.addSameLabel(this);
		}
	}
	
	protected void removeSameLabel(Label label) {
		sameLabels.remove(label);
		if (label != null && label.containsSameLabel(this)) {
			label.removeSameLabel(this);
		}
	}
	
	protected boolean containsSameLabel(Label label) {
		if (sameLabels != null)
			return sameLabels.contains(label);
		return false;
	}
	
	protected void removeAllSameLabels() {
		if (sameLabels == null)
			return;
		for (int i = 0; i < sameLabels.size(); i++) {
			removeSameLabel(sameLabels.get(0));
		}
	}
	
	private boolean hasSameLabel() {
		return (sameLabels != null && sameLabels.size() > 0);
	}
	
	public void computeLabels(Label[] labels) { //Can be made easier by using the entire drawing area as a single box.
		if (sameLabels != null)
			removeAllSameLabels();
		if (box.get() == null) {
			for (int i = 0; i < labels.length; i++) {
				if (!labels[i].equals(this) && labels[i].box.get() == null && labels[i].letter == letter) {
					addSameLabel(labels[i]);
				}
			}
		} else {
			for (int i = 0; i < box.get().labels.size(); i++) {
				if (!box.get().labels.get(i).equals(this) && box.get().labels.get(i).letter == letter) {
					addSameLabel(box.get().labels.get(i));
				}		
			}
		}
	}
	
	
	/*
	 * Improvement: avoid being placed inside another circle or close to another label.
	 */
	public void snapToCircle(Circle circle) {
		Point center;
		if (Math.abs(this.center.x - circle.center.x) == 0 && Math.abs(this.center.y - circle.center.y) == 0) {  //Check if on center circle then default to top left.
			center = new Point(this.center.x - circle.radius, this.center.y - circle.radius);
		} else {
			center = this.center;
		}
		double denom = Math.sqrt((center.x-circle.center.x)*(center.x-circle.center.x) + (center.y-circle.center.y)*(center.y-circle.center.y));
		if (denom == 0) return; //Shouldn't happen due to check above.
		
		double t = (circle.radius+LABEL_CIRCLE_DISIRED_DIST)/denom;
		
		this.center.x = (int) (t*(center.x-circle.center.x) + circle.center.x + 0.5); //0.5 for rounding.
		this.center.y = (int) (t*(center.y-circle.center.y) + circle.center.y + 0.5);
	}
	
	protected boolean hasCircle() {
		return circle.get() != null;
	}
	
	@Override
	public boolean isValid() {
		return (hasCircle() && !hasSameLabel()) || number != 0;
	}
	
	@Override
	public void draw(Graphics2D g2) {
		char[] array = {letter};
		if (!isValid()) {
			g2.setColor(Color.RED);
		} else {
			g2.setColor(Color.BLACK);
		}
		g2.setFont(new Font(g2.getFont().getFontName(),Font.PLAIN, FONT_SIZE));
		g2.drawChars(array, 0, 1, center.getX() - width/2, center.getY() + height/2);
		g2.setColor(Color.BLACK);
		if (number != 0) {
			array = String.valueOf(number).toCharArray();
			g2.setFont(new Font(g2.getFont().getFontName(),Font.PLAIN, FONT_SIZE-4));
			g2.drawChars(array, 0, array.length, center.getX() + width - 6, center.getY() + height/2 + 7);
		}
	}

	@Override
	public boolean intersects(Line line) {
		int width = Math.max(this.width, LABEL_MIN_WIDTH);
		Box box = new Box(center.x - width/2, center.y - height/2, width, height);
		return box.intersects(line);
	}

	@Override
	public void remove() {
		circle.set(null, null);
		box.set(null, null);
		removeAllSameLabels();
	}
}
