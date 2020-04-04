package tool;

import fdtmc.FDTMC;
import fdtmc.State;

public class FDTMCStub {

	public static FDTMC createOxygenationFDTMC() {
		FDTMC fdtmcOxygenation = new FDTMC();
		fdtmcOxygenation.setVariableName("sOxygenation");

		//States Creation
		State	init = fdtmcOxygenation.createInitialState(),
				success = fdtmcOxygenation.createSuccessState(),
				fail = fdtmcOxygenation.createErrorState(),
				source, target, target2;

		source = init;
		target = fdtmcOxygenation.createState();
		fdtmcOxygenation.createTransition(source, target, "register", "0.999");
		fdtmcOxygenation.createTransition(source, fail, "register", "0.001");

		source = target;
		target = fdtmcOxygenation.createState();
		fdtmcOxygenation.createTransition(source, target, "register_return", "0.999");
		fdtmcOxygenation.createTransition(source, fail, "register_return", "0.001");

		source = target;
		target = fdtmcOxygenation.createState();
		fdtmcOxygenation.createTransition(source, target, "sendSituation_SPO2", "0.999");
		fdtmcOxygenation.createTransition(source, fail, "sendSituation_SPO2", "0.001");

		source = target;
		target = fdtmcOxygenation.createState();
		fdtmcOxygenation.createTransition(source, target, "persist", "0.999");
		fdtmcOxygenation.createTransition(source, fail, "persist", "0.001");

		//SQlite selection / interface
		source = target;
		target = fdtmcOxygenation.createState();
		target2 = fdtmcOxygenation.createState();
		fdtmcOxygenation.createTransition(source, target, "sqliteSelection", "1");
		fdtmcOxygenation.createTransition(source, target2, "sqliteSelection", "0");
		State sucessSqlite = fdtmcOxygenation.createState();
		State failSqlite = fdtmcOxygenation.createState();
		source = target;
		fdtmcOxygenation.createTransition(source, sucessSqlite, "", "sqlite");
		fdtmcOxygenation.createTransition(sucessSqlite, target2, "", "1.0");
		fdtmcOxygenation.createTransition(source, failSqlite, "", "1-sqlite");
		fdtmcOxygenation.createTransition(failSqlite, fail, "", "1.0");

		//memory selection / interface
		source = target2;
		target = fdtmcOxygenation.createState();
		target2 = fdtmcOxygenation.createState();
		fdtmcOxygenation.createTransition(source, target, "memorySelection", "1");
		fdtmcOxygenation.createTransition(source, target2, "memorySelection", "0");
		State sucessMemory = fdtmcOxygenation.createState();
		State failMemory = fdtmcOxygenation.createState();
		source = target;
		fdtmcOxygenation.createTransition(source, sucessMemory, "", "memory");
		fdtmcOxygenation.createTransition(sucessMemory, target2, "", "1.0");
		fdtmcOxygenation.createTransition(source, failMemory, "", "1-memory");
		fdtmcOxygenation.createTransition(failMemory, fail, "", "1.0");

		source = target2;
		target = fdtmcOxygenation.createState();
		fdtmcOxygenation.createTransition(source, target, "persistReturn", "0.999");
		fdtmcOxygenation.createTransition(source, fail, "persistReturn", "0.001");

		source = target;
		target = success;
		fdtmcOxygenation.createTransition(source, target, "sendSituation_Oxygenation", "0.999");
		fdtmcOxygenation.createTransition(source, fail, "sendSituation_Oxygenation", "0.001");

		fdtmcOxygenation.createTransition(success, success, "", "1.0");
		fdtmcOxygenation.createTransition(fail, fail, "", "1.0");

		return fdtmcOxygenation;
	}



	public static FDTMC createPositionFDTMC() {
		FDTMC fdtmcPosition = new FDTMC();
		fdtmcPosition.setVariableName("sPosition");

		//States Creation
		State	init = fdtmcPosition.createInitialState(),
				success = fdtmcPosition.createSuccessState(),
				fail = fdtmcPosition.createErrorState(),
				source, target, target2;

		source = init;
		target = fdtmcPosition.createState();
		fdtmcPosition.createTransition(source, target, "register", "0.999");
		fdtmcPosition.createTransition(source, fail, "register", "0.001");

		source = target;
		target = fdtmcPosition.createState();
		fdtmcPosition.createTransition(source, target, "register_return", "0.999");
		fdtmcPosition.createTransition(source, fail, "register_return", "0.001");

		source = target;
		target = fdtmcPosition.createState();
		fdtmcPosition.createTransition(source, target, "sendSituation_POS", "0.999");
		fdtmcPosition.createTransition(source, fail, "sendSituation_POS", "0.001");

		source = target;
		target = fdtmcPosition.createState();
		fdtmcPosition.createTransition(source, target, "persist", "0.999");
		fdtmcPosition.createTransition(source, fail, "persist", "0.001");

		//SQlite selection / interface
		source = target;
		target = fdtmcPosition.createState();
		target2 = fdtmcPosition.createState();
		fdtmcPosition.createTransition(source, target, "sqliteSelection", "1");
		fdtmcPosition.createTransition(source, target2, "sqliteSelection", "0");
		State sucessSqlite = fdtmcPosition.createState();
		State failSqlite = fdtmcPosition.createState();
		source = target;
		fdtmcPosition.createTransition(source, sucessSqlite, "", "sqlite");
		fdtmcPosition.createTransition(sucessSqlite, target2, "", "1.0");
		fdtmcPosition.createTransition(source, failSqlite, "", "1-sqlite");
		fdtmcPosition.createTransition(failSqlite, fail, "", "1.0");

		//memory selection / interface
		source = target2;
		target = fdtmcPosition.createState();
		target2 = fdtmcPosition.createState();
		fdtmcPosition.createTransition(source, target, "memorySelection", "1");
		fdtmcPosition.createTransition(source, target2, "memorySelection", "0");
		State sucessMemory = fdtmcPosition.createState();
		State failMemory = fdtmcPosition.createState();
		source = target;
		fdtmcPosition.createTransition(source, sucessMemory, "", "memory");
		fdtmcPosition.createTransition(sucessMemory, target2, "", "1.0");
		fdtmcPosition.createTransition(source, failMemory, "", "1-memory");
		fdtmcPosition.createTransition(failMemory, fail, "", "1.0");

		source = target2;
		target = fdtmcPosition.createState();
		fdtmcPosition.createTransition(source, target, "persistReturn", "0.999");
		fdtmcPosition.createTransition(source, fail, "persistReturn", "0.001");

		source = target;
		target = success;
		fdtmcPosition.createTransition(source, target, "sendSituation_Position", "0.999");
		fdtmcPosition.createTransition(source, fail, "sendSituation_Position", "0.001");

		fdtmcPosition.createTransition(success, success, "", "1.0");
		fdtmcPosition.createTransition(fail, fail, "", "1.0");

		return fdtmcPosition;
	}



	public static FDTMC createSituationFDTMC() {
		FDTMC fdtmcSituation = new FDTMC();
		fdtmcSituation.setVariableName("sSituation");

		//States Creation
		State s0, s1, s2, s3, s4, s5, s6, s7, s8, s9,
			  s10, s11, s12, s13, s14, s15, s16, s17;
		s0 = fdtmcSituation.createErrorState();
		s1 = fdtmcSituation.createInitialState();
		s2 = fdtmcSituation.createState();
		s3 = fdtmcSituation.createState("plsRte_success");
		s4 = fdtmcSituation.createState("plsRte_error");
		s5 = fdtmcSituation.createState();
		s6 = fdtmcSituation.createState();
		s7 = fdtmcSituation.createState("oxy_success");
		s8 = fdtmcSituation.createState("oxy_error");
		s9 = fdtmcSituation.createState();
		s10 = fdtmcSituation.createState();
		s11 = fdtmcSituation.createState("temp_success");
		s12 = fdtmcSituation.createState("temp_error");
		s13 = fdtmcSituation.createState();
		s14 = fdtmcSituation.createState();
		s15 = fdtmcSituation.createState("pos_success");
		s16 = fdtmcSituation.createState("pos_error");
		s17 = fdtmcSituation.createSuccessState();

		//Transitions Creation
		fdtmcSituation.createTransition(s1, s2, "pulseRateSelection", "1");
		fdtmcSituation.createTransition(s1, s5, "pulseRateSelection", "0");
		fdtmcSituation.createTransition(s2, s3, "", "pulserate");
		fdtmcSituation.createTransition(s2, s4, "", "1-pulserate");
		fdtmcSituation.createTransition(s3, s5, "", "1.0");
		fdtmcSituation.createTransition(s4, s0, "", "1.0");
		fdtmcSituation.createTransition(s5, s6, "oxySelection", "1");
		fdtmcSituation.createTransition(s5, s9, "oxySelection", "0");
		fdtmcSituation.createTransition(s6, s7, "", "oxygenation");
		fdtmcSituation.createTransition(s6, s8, "", "1-oxygenation");
		fdtmcSituation.createTransition(s7, s9, "", "1.0");
		fdtmcSituation.createTransition(s8, s0, "", "1.0");
		fdtmcSituation.createTransition(s9, s10, "tempSelection", "1");
		fdtmcSituation.createTransition(s9, s13, "tempSelection", "0");
		fdtmcSituation.createTransition(s10, s11, "", "temperature");
		fdtmcSituation.createTransition(s10, s12, "", "1-temperature");
		fdtmcSituation.createTransition(s11, s13, "", "1.0");
		fdtmcSituation.createTransition(s12, s0, "", "1.0");
		fdtmcSituation.createTransition(s13, s14, "posSelection", "1");
		fdtmcSituation.createTransition(s13, s17, "posSelection", "0");
		fdtmcSituation.createTransition(s14, s15, "", "position");
		fdtmcSituation.createTransition(s14, s16, "", "1-position");
		fdtmcSituation.createTransition(s15, s17, "", "1.0");
		fdtmcSituation.createTransition(s16, s0, "", "1.0");


		return fdtmcSituation;
	}



	public static FDTMC createSqliteFDTMC() {
		FDTMC fdtmcSqlite = new FDTMC();
		fdtmcSqlite.setVariableName("sSqlite");

		State   init =fdtmcSqlite.createInitialState(),
				success = fdtmcSqlite.createSuccessState(),
				fail = fdtmcSqlite.createErrorState(),
				source, target;
		source = init;
		target = fdtmcSqlite.createState();
		fdtmcSqlite.createTransition(source, target, "persist", "0.999");
		fdtmcSqlite.createTransition(source, fail, "persist", "0.001");

		source = target;
		target = success;
		fdtmcSqlite.createTransition(source, target, "persist_return", "0.999");
		fdtmcSqlite.createTransition(source, fail, "persist_return", "0.001");

		fdtmcSqlite.createTransition(success, success, "", "1.0");
		fdtmcSqlite.createTransition(fail, fail, "", "1.0");

		return fdtmcSqlite;
	}

	public static FDTMC createMemoryFDTMC() {
		FDTMC fdtmcMemory = new FDTMC();
		fdtmcMemory.setVariableName("sMemory");

		//States Creation
		State init = fdtmcMemory.createInitialState(),
				fail = fdtmcMemory.createErrorState(),
				success = fdtmcMemory.createSuccessState(),
				source, target;

		source = init;
		target = fdtmcMemory.createState();
		fdtmcMemory.createTransition(source, target, "persist", "0.999");
		fdtmcMemory.createTransition(source, fail, "persist", "0.001");

		source = target;
		fdtmcMemory.createTransition(source, success, "persistReturn", "0.999");
		fdtmcMemory.createTransition(source, fail, "persistReturn", "0.001");

		fdtmcMemory.createTransition(success, success, "", "1.0");
		fdtmcMemory.createTransition(fail, fail, "", "1.0");
		//Transitions creation
//		fdtmcMem.createTransition(s2, success, "persistReturn", "0.999");
//		fdtmcMem.createTransition(s2, fail, "persistReturn", "0.001");

		return fdtmcMemory;
	}

	public static FDTMC createFileFDTMC() {
		FDTMC fdtmcFile = new FDTMC();
		fdtmcFile.setVariableName("sFile");

		//States Creation
		State 	init = fdtmcFile.createInitialState(),
				success = fdtmcFile.createSuccessState(),
				fail = fdtmcFile.createErrorState(),
				source, target;

		source = init;
		target = fdtmcFile.createState();
		fdtmcFile.createTransition(source, target, "persist", "0.999");
		fdtmcFile.createTransition(source, fail, "persist", "0.001");

		source = target;
		target = fdtmcFile.createState();
		fdtmcFile.createTransition(source, target, "write", "0.999");
		fdtmcFile.createTransition(source, fail, "write", "0.001");

		source = target;
		target = success;
		fdtmcFile.createTransition(source, target, "persistReturn", "0.999");
		fdtmcFile.createTransition(source, fail, "persistReturn", "0.001");
		fdtmcFile.createTransition(success, success, "", "1.0");
		fdtmcFile.createTransition(fail, fail, "", "1.0");


		return fdtmcFile;
	}


	public static FDTMC createPulseRateFDTMC() {
		FDTMC fdtmcPulseRate = new FDTMC();
		fdtmcPulseRate.setVariableName("sPulseRate");

		//States creation
		State s0, s1, s2, s3, s4, s5, s6, s7, s8, s9,
			  s10, s11, s12, s13, s14, s15, s16;
		s0 = fdtmcPulseRate.createErrorState();
		s1 = fdtmcPulseRate.createInitialState();
		s2 = fdtmcPulseRate.createState();
		s3 = fdtmcPulseRate.createState();
		s4 = fdtmcPulseRate.createState();
		s5 = fdtmcPulseRate.createState();
		s6 = fdtmcPulseRate.createState();
		s7 = fdtmcPulseRate.createState();
		s8 = fdtmcPulseRate.createState("error_sqlite");
		s9 = fdtmcPulseRate.createState();
		s10 = fdtmcPulseRate.createState();
		s11 = fdtmcPulseRate.createState();
		s12 = fdtmcPulseRate.createState("error_mem");
		s13 = fdtmcPulseRate.createState();
		s14 = fdtmcPulseRate.createState();
		s15 = fdtmcPulseRate.createState();
		s16 = fdtmcPulseRate.createSuccessState();

		//Transition
		fdtmcPulseRate.createTransition(s1, s2, "register", "0.999");
		fdtmcPulseRate.createTransition(s1, s0, "register", "0.001");
		fdtmcPulseRate.createTransition(s2, s3, "registerReturn", "0.999");
		fdtmcPulseRate.createTransition(s2, s0, "registerReturn", "0.001");
		fdtmcPulseRate.createTransition(s3, s4, "sendSituation", "0.999");
		fdtmcPulseRate.createTransition(s3, s0, "sendSituation", "0.001");
		fdtmcPulseRate.createTransition(s4, s5, "persist", "0.999");
		fdtmcPulseRate.createTransition(s4, s0, "persist", "0.001");
		fdtmcPulseRate.createTransition(s5, s6, "fSqliteSelection", "1");
		fdtmcPulseRate.createTransition(s5, s9, "fSqliteSelection", "0");
		fdtmcPulseRate.createTransition(s6, s7, "", "sqlite");
		fdtmcPulseRate.createTransition(s6, s8, "", "1-sqlite");
		fdtmcPulseRate.createTransition(s7, s9, "", "1.0");
		fdtmcPulseRate.createTransition(s8, s0, "", "1.0");
		fdtmcPulseRate.createTransition(s9, s10, "fMemorySelection", "1");
		fdtmcPulseRate.createTransition(s9, s13, "fMemorySelection", "0");
		fdtmcPulseRate.createTransition(s10, s11, "", "memory");
		fdtmcPulseRate.createTransition(s10, s12, "", "1-memory");
		fdtmcPulseRate.createTransition(s11, s13, "", "1.0");
		fdtmcPulseRate.createTransition(s12, s0, "", "1.0");
		fdtmcPulseRate.createTransition(s13, s14, "persistReturn", "0.999");
		fdtmcPulseRate.createTransition(s13, s0, "persistReturn", "0.001");
		fdtmcPulseRate.createTransition(s14, s15, "sendSituation", "0.999");
		fdtmcPulseRate.createTransition(s14, s0, "sendSituation", "0.001");
		fdtmcPulseRate.createTransition(s15, s16, "sendSituationReturn", "0.999");
		fdtmcPulseRate.createTransition(s15, s0, "sendSituationReturn", "0.001");

		return fdtmcPulseRate;
	}

}
