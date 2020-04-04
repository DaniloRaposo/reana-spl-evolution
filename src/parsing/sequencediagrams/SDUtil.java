package parsing.sequencediagrams;

import java.util.logging.Level;
import java.util.logging.Logger;

import parsing.Node;

/**
 * Set of static methods to deal with I/O for SDs
 *
 */
public class SDUtil {
    private static final Logger LOGGER = Logger.getLogger(SDUtil.class.getName());

	/**
	 * For DEBUG purposes only.
	 * Prints to STDOUT the information of a SD Fragment
	 * @param f a MagicDraw UML SD fragment
	 */
	private static String printFragment(Fragment f) {
		if (f.getName() != null && !f.getName().isEmpty()) {
			return "[Fragment = " + f.getName() + "]\n";
		} else {
			return "[Fragment = " + ((Operand) f.getNodes().get(0)).getGuard() + "]\n";
		}
	}

	/**
	 * For DEBUG purposes only.
	 * Prints to STDOUT the information of a SD Message
	 * @param m a MagicDraw UML SD message
	 */
	private static String printMessage(Message m) {
		return "[" + m.getName() + "]: "
				+ m.getSender().getName() + "->"
				+ m.getReceiver().getName() + " (" + m.getType()
				+ ") p = " + m.getProb() + "; egy: " + m.getEnergy() + "; ex: "
				+ m.getExecTime()
				+ "\n";
	}

	/**
	 * For DEBUG purposes only.
	 * Prints to STDOUT the information of a SD Fragment
	 * @param sd the Magic Draw UML Sequence Diagram
	 * @param indent the indentation being applied to the output
	 */
	private static String printInSequence(Fragment fragment, String indent) {
	    String message = indent;
		message += "Lifelines:\n";
		for (Lifeline l: fragment.getLifelines()) {
		    message += indent;
		    message += l.getName() + "\n";
		}
		message += "\n";

		message += indent;
		message += "Nodes:\n";
		for (Node n: fragment.getNodes()) {
		    message += indent;
			if (n.getClass().equals(Fragment.class)) {
				Fragment f = (Fragment)n;
				message += printFragment(f);
				message += printInSequence(f, indent+"\t");
			} else if (n.getClass().equals(Operand.class)) {
				Operand o = (Operand)n;
				message += "Guard = " + o.getGuard() + "\n";
				for (Node n1: o.getNodes()) {
				    message += indent;
					if (n1.getClass().equals(Message.class)) {
					    message += printMessage((Message)n1);
					} else if (n1.getClass().equals(Fragment.class)) {
						Fragment f = (Fragment)n1;
						message += printFragment(f);
						message += printInSequence((Fragment)n1, indent+'\t');
					}
				}
			} else if (n.getClass().equals(Message.class)) {
			    message += printMessage((Message)n);
			}
		}
		return message;
	}

	/**
	 * For DEBUG purposes only.
	 * Prints to STDOUT the important information of a SDReader instance,
	 * following a format that facilitates DEBUGGING
	 * @param sdr
	 */
	public static void printAll(SDReader sdr) {
	    if (LOGGER.isLoggable(Level.FINER)) {
	        String message = "Sequence Diagram "+ (sdr.getIndex() + 1) + ": " + sdr.getSD().getName() + "\n\n";
	        LOGGER.finer(message + printInSequence(sdr.getSD(), ""));
	    }
	}

}
