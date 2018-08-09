package casino.contract.exceptions;

public class RequireViolationException extends Exception {

	/**
	 * 
	 */
	private static final long serialVersionUID = 3458879323181782001L;

	/*@ public normal_behavior 
	  @ ensures true;
	  @ assignable \nothing;
	  @*/
	public RequireViolationException() {		
	}
	
}
