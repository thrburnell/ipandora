import { connect } from 'react-redux'
import FormulaList from '../components/FormulaList'
import { selectFormulaAsJustification } from '../actions'

const mapStateToProps = (state) => (
  {
    formulas:  state.givens.map(key => state.knownFormulas[key]),
    clickable: state.proofStepState != 'AWAITING_VALIDITY_CHECK'
  }
)

const mapDispatchToProps = (dispatch) => (
  {
    onFormulaClick: (id) => dispatch(selectFormulaAsJustification(id))  
  }
)

const RGivenList = connect(
  mapStateToProps,
  mapDispatchToProps
)(FormulaList)

export default RGivenList

