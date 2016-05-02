const knownFormulas = (state = {}, action) => {

  switch (action.type) {
    // ADD_GIVEN and ADD_PROOF_STEP behave identically
    case 'ADD_GIVEN':
    case 'ADD_PROOF_STEP':
      return {
        ...state,
        [action.id]: {
          id: action.id,
          uiId: action.uiId,
          formula: action.formula
        }
      }

    default:
      return state
  }

}

export default knownFormulas

