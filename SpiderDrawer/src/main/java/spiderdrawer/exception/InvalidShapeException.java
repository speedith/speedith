package spiderdrawer.exception;

public class InvalidShapeException extends Exception {

	private String shape;
	
	public InvalidShapeException(String shape) {
		super();
		this.shape = shape;
	}
	
	public String getShape() {
		return shape;
	}
	
	@Override
	public String getMessage() {
		return "Invalid shape: " + shape + ".";
	}
	
}
