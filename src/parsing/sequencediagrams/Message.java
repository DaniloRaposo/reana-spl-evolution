package parsing.sequencediagrams;

import parsing.Node;

public class Message extends Node {
	private String name;
	private Lifeline sender;
	private Lifeline receiver;
	private MessageType type;

	public Message(String id) {
		super(id);
	}

	public void setName(String name) {
		this.name = name;
	}

	public String getName() {
		return this.name;
	}

	public Lifeline getSender() {
		return this.sender;
	}

	public void setSender(Lifeline sender) {
		this.sender = sender;
	}

	public void setReceiver(Lifeline receiver) {
		this.receiver = receiver;
	}

	public Lifeline getReceiver() {
		return this.receiver;
	}

	public MessageType getType() {
		return type;
	}

	public void setType(MessageType type) {
		this.type = type;
	}

}
