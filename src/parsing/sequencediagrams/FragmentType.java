package parsing.sequencediagrams;

import parsing.exceptions.UnsupportedFragmentTypeException;

public enum FragmentType {
	LOOP,
	ALTERNATIVE,
	OPTIONAL,
	PARALLEL;

	/**
	 * gets the Fragment Type from the typeName
	 * @param typeName
	 * @return
	 * @throws UnsupportedFragmentTypeException
	 */
	public static FragmentType getType(String typeName) throws UnsupportedFragmentTypeException {
		if ("opt".equals(typeName)) {
			return OPTIONAL;
		} else if ("alt".equals(typeName)) {
			return ALTERNATIVE;
		} else if ("loop".equals(typeName)) {
			return LOOP;
		} else if ("par".equals(typeName)) {
			return PARALLEL;
		} else {
			throw new UnsupportedFragmentTypeException("Fragment of type " + typeName + " is not supported!");
		}
	}
}
