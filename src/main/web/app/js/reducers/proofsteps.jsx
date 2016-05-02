const proofSteps = (state = [], action) => {
  switch (action.type) {
    case 'ADD_PROOF_STEP':
      return [
        ...state,
        {
          derived: action.id,
          justifications: action.justifications
        }
      ]
    default:
      return state
  }
}

export default proofSteps

