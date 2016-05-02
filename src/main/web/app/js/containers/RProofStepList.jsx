import { connect } from 'react-redux'
import JustifiedFormulaList from '../components/JustifiedFormulaList'

const mapStateToProps = (state) => (
  {
    formulas:
      state.proofSteps.map(({ derived, justifications }) => (
          {
            ...state.knownFormulas[derived],
            justifications
          }
      ))
  }
)

const RProofStepList = connect(
  mapStateToProps
)(JustifiedFormulaList)

export default RProofStepList

