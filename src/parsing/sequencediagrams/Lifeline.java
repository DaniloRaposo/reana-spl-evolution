package parsing.sequencediagrams;

public class Lifeline {
	private String id;
	private String name;
	private String link;

	public Lifeline(String id) {
		this.id = id;
	}

	public String getId() {
		return id;
	}
	public void setName(String name) {
		this.name = name;
	}

	public String getName() {
		return this.name;
	}

	public void setLink(String link) {
		this.link = link;
	}

	public String getLink() {
		return this.link;
	}

}
